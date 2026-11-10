# Packet 14a (Cauchy §10.1–§10.2), round 5, 9 Nov 2026

## Pre-check of cauchy-p14a-20261109-r5 (narrow)

- **Lines under review:** #C10.1.3-0, #C10.1.4-1-1-1, #C10.1.6-1, #C10.2.1–#C10.2.1-0-1, and #C10.2.3. These are r4's repaired lines (WILSON_IT1_LF_TRIAGE_P14A_R4_2026_11_09.md). The rest of 14a, reviewed in r4, is context, with the consumers #C10.3.3-6–#C10.3.3-10, #C10.4.1–#C10.4.1-1, and #C10.4.7-7.
- **Every changed line re-read** on 9 Nov 2026, with PBG p.396 l.14–30 (the class of cubes, (3.35)–(3.36)), p.416 (Theorem 3.11 and its proof), and p.423 l.20–36 (Theorem 3.12) in the corrected transcription.
- **Repairs made in this pre-check (adversarial pass on #C10.2.1-0):**
  - "Real pair" was not defined. #C10.2.1 now says "U and J real".
  - #C10.2.1-0 used A real without saying why. It now states that εA, of norm < εα₁/a_j, is the small logarithm of UU₀^{−1} ∈ G, which lies in 𝔤, so the path e^{itεA}U₀ is real.
  - #C10.2.1 claims Q_m onto in both cases, but #C10.2.1-0 argued only the positivity. It now ends "In both cases Q_m is onto by #C10.1.6-1".
- **Re-derived:**
  - First case: Theorem 3.12 states that Theorem 3.11 holds for G₁ under (3.35)–(3.36). Theorem 3.11's proof uses G = G₀(I − R)^{−1} with R small and the positivity of G₀; for G₁ the series (3.138) plays the role of R. (3.36) enters only through the current's size (#C10.3.3-6), so the variant with |J| ≤ α_Jℓ^{−3} keeps the positivity of G₁, hence of G₁^{−1}.
  - Second case: (tA) satisfies |tA| < α₁/a_j and |∇(tA)| < α₁/a_j², so every point of the path is a real pair of 𝒟_j. G₁(t)^{−1} = Δ₁ + DRD* + aℓ^{−2}Q_m*Q_m is the operator of a real quadratic form, hence symmetric. It is invertible with inverse the series (3.138), convergent on 𝒟_j (#C10.3.3-8), and continuous in t by the analyticity of #C10.3.3-10. The eigenvalues of a continuous family of symmetric invertible operators on the finite torus cannot cross 0.
  - Cube containment (#C10.2.1-0-1): a cube of the class at the scale ℓ has side κℓ, κ ≥ 10M, and is a union of big blocks of side Mℓ (p.396 l.15–16). The union of the big a_j-blocks meeting it is a cube of side ≤ κℓ + 2Ma_j, so κ′ ≤ max(10M, κ/L + 2M) ≤ Lκ (κ ≥ 10M, L ≥ 2). Then κ′α₀a_j^{−1} = (κ′/L)α₀ℓ^{−1} ≤ κα₀ℓ^{−1} and κ′α₀a_j^{−2} = (κ′/L²)α₀ℓ^{−2} ≤ κα₀ℓ^{−2}. The gauge u of the larger cube, restricted, serves for the smaller one.
  - #C10.1.6-1's third case: at the current 0, #BX.1-3's hypothesis abs(𝐉) < γ(L^jη)^{−3} holds strictly for every γ > 0.
  - #C10.2.3: the identity uses only Q_mH₁B = B and the two inverses, which BP_PBG_COMPLEX gives on 𝒟_j. With the bilinear pairing and the transpose, annihilation replaces orthogonality.
- **Grep of touched claims:** "real pair" occurs only in #C10.2.1–#C10.2.1-0. #C10.3.3-12 is deleted and cited nowhere (Cauchy, LF, balaban_proofs/). #C10.4.7-7 and the Assembly use the positivity at the pair of §10.4, a real pair of 𝒟_j (#C10.4.1–#C10.4.1-1).
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (4 allowed: Y_c, U₁, X, ℓ).
- **Size:** the reviewed lines are 3.63k characters, and 14a is 14.09k (25k cap). CR is 0, and there are no trailing spaces or duplicate tags. Lines 1802–1804 are 424, 578, and 440 characters.
- **Spec:** specs\spec_p14a_r5.json (Cauchy 14ee33c357e1, LF 6ac728004094). Claim (d) states that A is real at a real pair and that Q_m is onto in both cases. Question 4 asks about the reality of A.
- **Order:** after 14bp r5 (full). Rebuild at launch.

Written 2026-11-09 08:53.

## Pre-check update (09:38)

- **Re-pointings in the part** (bookkeeping, after 14b1 r3 re-cut #C10.3.3-8–#C10.3.3-10): #C10.1.6-1 now cites #C10.3.3-9 for BX's conditions M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx, and #C10.2.1-0 cites #C10.3.3-9 for the convergent series (3.138). The text at those tags is the same.
- **Context changes:** 14b1 r3's repairs (#C10.3.3–#C10.3.3-1, #C10.3.3-6–#C10.3.3-10-1, #C10.3.3-11-6–#C10.3.3-11-7-0) and §10.4's #C10.4.1-1–#C10.4.1-1-1. The part's #C10.2.1 and #C10.2.1-0-1 are cited by #C10.3.3-1 and #C10.4.1-1 for the cube argument, unchanged.
- **Other files:** the LF is 73435a4a8e2a (#4.101–#4.101-1, PBG's a = 1 and the recursion for i ≥ 1), not cited by the part. The table is 0e8cb42f87e0 (LABELS 22c9a3403920).
- **Spec:** update to Cauchy 21a4ba1b0dd3 and LF 73435a4a8e2a at launch, re-run the definition check, and rebuild.

## Round 5, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line under review and its context against PBG p.396, p.416, p.419, p.422–423, and CMP 98 in the corrected transcriptions.
- **Verdict:** not clean; one minor.
- **Minor, #C10.1.6-1.** Its first case named the hypotheses of PBG Theorem 3.12, while #C10.2.1-0 applies Theorem 3.12 under the variant with the current bound in the place of (3.36). Repaired: it now reads "under the hypotheses of PBG Theorem 3.12 at the scale L^nη, or under their variant with the current bound in the place of (3.36) (#C10.2.1 at ℓ), by Theorem 3.12, with #C10.3.3-6 for the variant, and (3.132)". #C10.3.3-6 holds the reason: PBG's proof uses (3.36) only for the size of the current.
- **Checked and correct:** the cube containment (#C10.2.1-0-1), the reality of A and the continuity argument (#C10.2.1-0), the Galerkin identity (#C10.2.3), and #C10.1.4-1-1-1's list of CMP 98 results against every use in the note.
- **Changed since, in the part:** #C10.1.3-3 now defines δ₂ := min(δ₁′, ½δ₁) (15c r1's m4).
- **Next round:** r6, narrow, on #C10.1.6-1 and #C10.1.3-3, at Cauchy 282155b15f71.

Written 2026-11-09 16:41.
