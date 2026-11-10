# Triage of Packet 11, First Review (lf-p11-20261105-r1)

The review is verification/isolated_reviewer/reviews/lf-p11-20261105-r1/review.md, a full round, at the LF aff9348d04ab, the table 0441886c6eef, and the labels index 37b91acfac94.

It found no fatal finding, one serious finding, S1, and nine minor findings, M1–M9. The round is not clean. Every finding is accepted, and each is repaired in the LF and, where its constants are recorded, in the table and W-δ. The repaired files and their SHAs are listed at the end.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| S1. #4.40–#4.42 use the uniform ρ̄ of #4.9-3, whose factor (ε/a_n)^{1−ε₀} is set by the finest layer of the problem; with older, finer layers present this does not give the per-point bound at the history's points | serious | correct; the case occurs (#4.39 allows it) | #4.40 uses #4.38's ρ̄(x) point by point, with the gap per point in (ε/a_{j(x)}) and C′_gap with c″_K. #4.40.1-1 to #4.40.1-3 give the quadratic kernel form of D and the π-weighted bounds of HD(A₁*), HC^{(2)}(A₁*), V(A₁*), and the local terms, each ≤ Cρ̄(x)² per point. #4.40.2 is π-weighted: the factor L^{3n}, C_ℒ^π := 4L³C_ℒ^{ker}c_ε, under ½δ_Q^{pl}RM ≥ 3 log L + 1 (LM₁ at the joins). #4.29, the table rows, and W-δ #W8.18-4 and #W8.19-4 carry the new condition |
| M1. #4.12 and #0.17 justify the width of the layer h of 𝐁″_k by CRE p.256 l.21–23, but on Z that layer is Ω_h ∖ Ω^{∼5}_{h+1} | minor | correct | #4.12 and #0.17: the layers j ≤ h − 1 are CRE's; the layer h on Z is Ω_h ∖ Ω^{∼5}_{h+1}, at least 3LMR_{h+1} wide by #4.18-1's argument at j = h |
| M2. #0.17 and #4.18 call printed what is inferred from LFR I p.178 and the condition (ii); the absence of R-operation domains in Z is not argued | minor | correct | Both now say "inferred from LFR I p.178 and the condition (ii)", and #4.18-0 argues the absence of R-operation domains in Z within the last N steps |
| M3. "R′ needs no separate threshold" is a reading against PBG's "R, M sufficiently large" | minor | correct | #4.22-2 and #4.22-2-1: K_{M′} ≥ R_thr(d, L)/L + 1, a further lower bound, which #4.24 cites in place of its earlier sentence; table #T2.15 and W-δ #W8.16-2 |
| M4. #4.7's regularity at a_j holds only up to L³ near the outer layer boundaries and in the thin top layer of 𝐁₂ | minor | correct | #4.7-1 and #4.7-2: the bounds hold with C₀^{ms} := L³C₀ at every point, and the constants below are taken at C₀^{ms} (C₀′ is the table's #T4.5) |
| M5. The kernel form leaves the terms of VAR (39) after (47) and VAR's sketched variants of (91)–(96) unenumerated | minor | correct | #4.36-2 and #4.36-3 list them with their link patterns |
| M6. #4.41 does not cite the bound on ∇w, omits the weighted blocking artefact and the quadratic remainder, and pairs J_w with A₁* | minor | correct | #4.41-1 to #4.41-3: the bound on a·abs(∇w) from LFR II p.360 l.34–35 and CRE (2.24); b_w and the quadratic remainder; the pairing with A′* at #4.38's ρ̄(x) |
| M7. C_h depends on g_a, which is not listed | minor | correct | #4.42-1 writes C_h and lists g_a, uniform by the continuum note's #ND.1.2 |
| M8. #4.25's "□̃₀⁵ = □̃⁸ is not exact" mixes two objects | minor | correct | #4.25: □̃₀⁵ = □̃⁷ ⊂ □̃⁸, and X̃⁵ of X = □̃⁴ is □̃⁹ |
| M9. K is CRE's ratio M₁/M′, PBG's K, and the Cauchy index; ρ̄ is used with and without x | minor | correct | The ratio is renamed K_{M′} in the LF, the table, and W-δ; the uniform ρ̄ of #4.9-3 is renamed ρ̄_u (ρ̄_n is §5's sup_xρ̄(x)); the kernel K(y,y′) is renamed K_ρ(y,y′) |

## Repaired Files

- WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md (the LF): cb837216d36b. The new lines over 600 characters are split into tagged lines (#4.22-2-1, #4.36-2-1, #4.36-3-1, #4.40-0, #4.40.1-0, #4.40.1-0-1, #4.40.1-1-0, #4.42-0).
- CONSTANTS_AND_CONVENTIONS_WDELTA.md (the table): 27240a89f01e, 208 rows.
- WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md (W-δ): 282930180da7.
- LABELS_LF_AND_TABLE.md (the labels index): 2a281cf22f8a, 102 multiply defined.
