# Packet 11b r1 Triage (LF #4.30–#4.42-2)

Review: verification/isolated_reviewer/reviews/lf-p11b-20261106-r1/review.md (full round of part 11b), on LF 36c22ebe3cfa, labels 8a80856836c4, and table 697a56eb4c81. The run used the config directory .claude-IF. The reviewer reports the automatically supplied AGENTS.md context, as the 11a rounds did.

## Verdict

r1 has no fatal or serious finding. It has eight minor ones (m1–m8), so it is **not clean**. Every named step is CORRECT except #4.42-2 (UNCLEAR, m1). Each finding is repaired below by rewording the existing sentence.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m1 | #4.42-2 | "the per-point bound is that of the single-scale (9.10)" now reads "the stopping layer k, where w = 0 (#4.41-1) and the per-point bound C_b(ε/a_k)ε₁² + C′_gap(ε₀)(ε/a_k)^{2−2ε₀}ε₁² (#4.8, #4.40-1) is that of the single-scale (9.10) once C′_gap(ε₀)L^{−(1−2ε₀)k} ≤ C_b, a condition that joins §9's k₀(ε₀) (#C9.6.3)". |
| m2 | #4.40 | "up to the non-local links ℒ and H of #4.40.1" now adds "and V(A₁*), non-local through 𝒩 and bounded by the kernel form in #4.40.1-3-1". |
| m3 | #4.40-0 | The display now reads "\|A_ε(Ũ) − A_ε(U^A)\| ≤ Σ_x…". |
| m4 | #4.40.1-0 | "carries the regularity (#4.7) of a layer of x or of x′" now reads "carries the regularity (#4.7-2) at a point near x or x′, whose layer is at most one finer than theirs, the factor ≤ L of its spacing being taken into C_ℒ^{ker}". |
| m5 | #4.41 | "the first-order term of the gap does not vanish" now reads "the first-order term is not (9.7)'s db(U^B)[ℒA₁*] (#4.40.1) and lacks its ε/a". |
| m6 | #4.41-1-1 | The chain now ends "with {#D.g_−1} g_{−1} := g_0". |
| m7 | #4.42-1 | "since θ̃ ≥ L^{−(1−2ε₀)}" now reads "since θ̃ ≥ L^{−(1−ε₀)/4} ≥ L^{−(1−2ε₀)} (#3.39, 3 − 7ε₀ > 0)". |
| m8 | #4.40.1-2-2 | "(3.133) bounds H and ∇H each at B_H" now reads "(3.133) bounds H at B_H and ∇H at B_H times (L^jη)^{−1}, which the weight a_{j(x)}² against a_{j(x)} absorbs". |

## Pre-check

- **m1.** By #4.41-1, supp ζ₁ ⊂ Z″_{h+1}, which lies in the layers ≤ h < k, so w = 0 on the stopping layer. There the unweighted summand is the artefact's C_b(ε/a_k)ε₁² plus #4.40-1's gap term, with ε/a_k = L^{−k}. C′_gap(ε₀)L^{−(2−2ε₀)k} ≤ C_bL^{−k} is exactly C′_gap(ε₀)L^{−(1−2ε₀)k} ≤ C_b. That is a largeness condition on k of the same kind as #C9.6.3's C_gap(ε₀)L^{−(1−2ε₀)k} ≤ C_b, and §9 asserts (9.10) only for k ≥ k₀(ε₀) (#C9.6.6).
- **m4.** #4.7-2 gives the regularity at every point, under either indexing, with C₀^{ms}. Each layer is wider than RM in its own units (#4.40.1-3), so a point next to x or x′ lies at most one layer finer, and its spacing is ≥ a_{x,x′}/L. C_ℒ^{ker} is one of the constants §9 builds from C₀, taken at C₀^{ms} (#4.7-2-1), and it remains a constant of L, d, G, and C₀ with the factor L included.
- **m6.** At j(x) = 0 the layer value is g_0^{−2}, so the chain holds with g_{−1} := g_0.
- **m7.** (1 − ε₀)/4 ≤ 1 − 2ε₀ is equivalent to 7ε₀ ≤ 3, and ε₀ < 2/5 (§5, as #3.39 uses it).
- **m8.** At p.422 l.26, ∇H carries the extra (L^jη)^{−1}. a_{j(x)}²|∇HX| against a_{j(x)}|HX| absorbs it, so C_{HX} is unchanged.
- **Consumers.** No line other than #4.40-0 quotes the one-sided display. #4.42-2 is cited only by the labels index. The constants C′_gap(ε₀), C_ℒ^π, C_{HX}, C_∇, C_w(ε₀), and C_h, and the table rows #T4.33–#T4.35, are unchanged.
- **Lines.** The edited lines have at most 604 characters. CR 0; the labels index is rebuilt, and every citation resolves. g_{−1} is defined once.

## Repaired files

LF 039f871a34db, labels 0d3d3e21e38e, table 697a56eb4c81 (unchanged).
