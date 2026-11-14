# Packet 11 r18 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r18/review.md (full round), on LF 488d57f31aae, labels 31c594f34c04, and table 3a1f61afdbe0.

## Verdict

r18 has no fatal or serious finding. It has two minor findings, m-1 and m-2, and three trivial findings, t-1 to t-3, with one remark. So it is **not clean**. r17's points are resolved. r19 reviews the changed lines; a full round follows if r19 is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.41-2, new #4.41-2-1, #4.42; table #T4.35 | J_∇ is counted (#4.41-2, written there with absolute values): §9.6 bounds wJ by 8C₀^{ms} times the modulus of w times ε₁/a³; for J_∇ each w-difference is at most ε times the modulus of ∇w (the convention of #4.41-3), times a plaquette deviation ≤ 2C₀^{ms}ε₁ε²/a² (#4.41-3-3), on six plaquettes, so the coefficient is 12; J_w is bounded with 12, the pairing gives 48, and C_w's first coefficient is 96 (as 48 × 2 from ρ̄ = 2C_Gc″_K(ε/a)^{1−ε₀}ε₁). |
| m-2 | #4.338 | The width list now reads W = RM on PRT2's sequences, W = LM on the frozen layers, and W ≥ LM₁ for every other layer of 𝐁″_k and of the joins (#4.17, #4.18-1, #4.18-2-2). |
| t-1 | new #4.12-1-0; #4.9-1, #4.12-1, #0.17-1, #4.14-2-1, #4.530-1 | CRE p.256 l.21–24 bounds the distance between the boundaries of Ω_j and Λ_j. The layer width follows from Ω_{j+1} ⊂ Λ_j ⊂ Ω_j (CRE (2.1)). The five lines now cite #4.12-1-0 instead of the bare pin. |
| t-2 | #4.24 | M ≤ M(ε₁) is pinned at VAR p.279 l.17. |
| t-3 | #4.24, #4.26 | The REG p.098 pins are corrected against the file: l.7–9, l.18–19, l.36–37 (twice), l.37–38. |
| remark | #4.41-1-3-2 | It agrees with CRE (2.3), Z_j = Λ_j^c (p.255 l.25). The reading keeps its label. |

## Pre-check

- **Sources read.**
  - CRE p.256 l.21–23: "the distance between their boundaries is at least equal to 2MR_j".
  - CRE (2.1), p.254 l.50: Ω_j ⊃ Λ_j ⊃ Ω_{j+1}.
  - CRE (2.3), p.255 l.25.
  - VAR p.279 l.17 (M ≤ M(ε₁)) and l.28 (its value).
  - REG p098.tex: l.7–9 ("a union of cubes of the size R₁M₁L^jη", "M is a multiple of R₁M₁"), l.8 ("smallest integers"), l.18–19 (□̃ and L^{−1}RM > 2dR₁M₁), l.36–37 (α₀ ≤ O(1)(R₁M₁)^{−1}), l.37–38 ("Applying Lemma 1 many times").
- **Arithmetic.**
  - ε^{−3}·6·ε\|∇w\|·2C₀^{ms}ε₁ε²/a² = 12C₀^{ms}\|∇w\|ε₁/a² = 12C₀^{ms}(a\|∇w\|)ε₁/a³.
  - 8\|w\| + 12a\|∇w\| ≤ 12(\|w\| + a\|∇w\|).
  - 4 × 12 = 48 and 48 × 2 = 96.
  - The second term of C_w, 4C_hes^wL⁶C_G²c″², is unchanged.
- **Every use.**
  - C_w is used symbolically in the Cauchy note (#C6.2.18-5 area, X^{cl}_K) and in LF #4.42-1 (C_h). Only #T4.35 recorded the coefficient, and it now reads 96. I announced the table edit to the fork first.
  - No line cites #4.41-2 for the pairing bound, which is now #4.41-2-1.
  - #4.317-0 already states the widths of #4.338's corrected list.
  - The pins are same-length substitutions in the long lines #4.24 and #4.26; no paragraph grew.
- **Lines.**
  - The new and changed lines are under 600 characters, except the pre-existing long lines #4.9-1, #4.24, and #4.26. #4.9-1 got shorter.
  - CR 0 in both files; no duplicate tags.

## Repaired files

LF 5bac61c02c1f, table 39fe437e0921, labels b8de63b42e23 (multiply defined 101).
