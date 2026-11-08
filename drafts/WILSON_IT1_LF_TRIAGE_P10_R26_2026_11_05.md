# Triage of Packet 10, Twenty-Sixth Review (lf-p10-20261105-r26)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r26/review.md, a full round, at the Cauchy note b7c584f0e065, the LF 7cebf9e4092c, and the table 6b71cece39e8.

It confirmed the r25 repairs. It found:

- no fatal or serious finding;
- one minor finding, M1;
- five cosmetic findings, C2 to C6;
- one packaging defect.

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note f3c1e73758b6, now tagged throughout and cited by tag (LABELS_CAUCHY.md);
- the LF a17196e50eb7;
- the table f8cdf4eadfed;
- the labels index e6b4ce94867a.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| M1. The young pairs' small-field exponent on Λ_k is carried in (6.2) and (6.3), but it is dropped from their tally, from b^{(M)}_K, and from §7 | minor | correct | The step is re-derived, not patched. §7 now defines X_K, the all-small-field relative bound ((7.1), #C7.3), with x_K := e^{X_K} − 1, and shows that the all-small-field pairs change F by ≤ 3x_KB_W (#C7.4). The bound holds at the young pairs' backgrounds (#C6.2.18). §6.2 bounds the relative difference on the common support by exp(X_K + Σφ′) − 1 (#C6.2.9-1, #C6.2.20-3), so (6.2) and (6.3) carry s_K + x_K (#C6.2.13, #C6.2.15). The numerators and the F change are re-counted (#C6.2.22), giving b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 5s_K + 3x_K + s^{W,tot}_K for k ≥ k_*. The total a_K := 3x_KB_W + b^{(S)}_KB_W + δ_LF(a^{(U)}_K + b^{(M)}_K)B_W (#CP.29) now carries the all-small-field factor B_W, which the earlier tally also lacked. Summability includes x_K ≤ X_Ke^{X_K} (#C6.2.17). The threshold k_* is a paragraph of its own (*The threshold.*, #C6.2.19), as are the smaller k (#C6.2.21). The LF's #5.63 now points to #C6.2.22 |
| C2. VAR p.293 prints D^*RD, and the note's DRD* is not marked as an emendation | cosmetic | correct | #C9.4.1-2: "which prints Δ₁ + D^*RD + aQ^*Q; DRD* is the reading of p.294 l.4–5 and l.18 and of PBG (3.153), the only one defined on bond fields" |
| C3. Table #T4.33 says that B₁^{REG} is not VAR's B₁ | cosmetic | correct | #T4.33: B₁^{REG} is VAR's B₁ of (19) (p.281 l.19), the B₁ of REG's (1.36), which REG Proposition 6 applies (p.099 l.28–32), with B₁ = 5dLB₀ (REG p.087 l.16) |
| C4. RG I prints Theorem 2 with its proof deferred | cosmetic | correct | #C1.1-2: "by BETA_FUNCTION_WILSON_LOOPS.md Corollary 8.2 for compact simple G, SU(2) included; RG I states this as its Theorem 2 for SU(2) and defers the proof to a separate paper (p.259 l.38)" |
| C5. The dimensionless B is sized per fine bond in units of (ε/L)^{−1} | cosmetic | correct | #C9.8.14-3 sizes B dimensionlessly (≤ C_LC_Fε²ε₁/a² per fine bond). #C9.8.14-4 adds the factor (L^jη)^{−1} ≤ L/ε of VAR's solution map (190), so B enters T as a source of size ≤ LC_LC_F(ε/a)ε₁/a |
| C6. The glossary lists B₀ and B₁ twice with different sources | cosmetic | correct | #CK.1-1: "B₀, B₁ (CRE (2.42), (2.47); not VAR's B₀, B₁ of §9)". The §9 entry reads "(VAR (49), (97), (117)–(121); this B₀, B₁ not CRE's of the boundary terms above)" |
| Packaging. The l.966 extract is empty | packaging | correct | The packet builder takes extracts by tag, so an extract cannot fall on a moved line |

The review's remark under S9.6 says that §9 asserts nothing for k < k₀(ε₀), so the callers must cover those k. Checked against the note, this was a gap. §8.3 and §10.5 use the depth source e_{k+1} at every step k, and §7 uses the classical group at every K. It is repaired as follows:

- §8.3, *The first steps.* (#C8.3.3-6 to #C8.3.3-8): at k < k₀(ε₀), d_{k+1} ≤ 2 by the plain class bound of both runs' terms (#C5.8-25), and C_e ≥ 2L^{k₀(ε₀)} keeps e_i ≤ C_eθ̃^i at every i, since θ̃ > L^{−1}.
- §9.6, *The smaller k.* (#C9.6.6): the scope of §9 and the two places that cover the smaller k.
- §7, *The smaller K.* (#C7.4-7, #C7.4-8): a_K := 2B_W for the finitely many K < K₁, where K₁ also covers the K₀(L, δ₀M₁, j(C)) of #C5.101-2. #CP.29-4 records this.
- The glossary's stale "K₀ (§6.1)" now reads K₀(L, δ₀M₁, j(C)) (§5) and K₁ (§7).

The Cauchy note is now f3c1e73758b6.

The note also changed beyond the repairs:

- #TP.1 no longer names line revisions. Cauchy and LF citations are tags; bare numbers are W-δ lines until W-δ is tagged.
- The LF's lines over 2,000 characters are split into tagged continuation lines (#P.2), with the wording unchanged.
- Twelve LF definition anchors now carry their own :=.

None of these changes alters any mathematics.

The next round is a full round over the whole packet. A clean pair must end with a full round, and M1 and the smaller k changed §6.2, §7, §8.3, and §9.6.
