# Triage of lf-p13b-20261108-r11

## Verdict

- r11 was a narrow round of 13b at LF 355391e734a7, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.52-1–#4.52-1-2, #4.556–#4.556-1, and #4.567–#4.568.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1: #4.52-1-1.1's evidence. LFR I p.197 l.10 is REG (1.65) at the base Q^{s*}_kV_Λ, not at the base 1, and the bridge between the two bases was not stated.
- **Observations:** four, o1–o4.
- The round is not clean, so 13b's clean count stays 0.
- Round 10's m1, m2, o1, o3, and o4 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.52-1-1.1 | l.10 bounds abs(M^j(U_0) − Q^{s*}_{k−j}V_Λ) with no α₁ term, so it is (1.65) at the base Q^{s*}_kV_Λ. The base-1 conditions follow only because Q^{s*}_kV_Λ is 1 inside the k-blocks | The line now reads "... whose (1.65) [14] with the constant 11d² and no α₁ term is REG (1.65) (p.087 l.36–44), REG's bound on the averages Ũ′^j of (1.19)–(1.20), at the base Q^{s*}_kV_Λ: since Q^{s*}_kV_Λ is 1 on the bonds inside the k-blocks (CRE (1.3), p.246 l.39–44, with k-blocks for 1-blocks, p.257 l.34), its averages are 1 on the contours, and its conditions (1.19) are those at the base 1." I checked CRE p.246 l.39–44 ((Q₁^{s*}V)(b) = 1 for b ⊂ B(y)) and p.257 l.34 ("only 1-blocks are replaced by k-blocks"). The scale-n averages on a contour bond inside a k-block involve only fine bonds of that k-block, so they are 1 |
| o1 | #4.52-1-1.1 | (1.19) at the base 1 is REG's axial gauge (1.15), with its own uniqueness statement | "(1.19) at the base 1 is REG's axial gauge (1.15) (p.078 l.29–38)". Checked: l.29–36 print (1.15), and l.38 reads "these equations together with (1.14) ... determine uniquely an element in each orbit". This is placed in #4.52-1-1.1 so that #4.52-1-1 stays near 600 characters. #T11.33's "not the absolute axial gauge (1.15)" holds for a general base; the fork is asked to say so |
| o2 | #4.52-1-2 | "at the shared levels" should say that these are all of run A's levels n < k inside Λ | "..., which are all of run A's levels n < k inside Λ (#4.5-2)". #4.5-2 gives Ω^B_{m+1} = Ω^A_m, and Λ lies in the top layer (#4.44-0.2) |
| o3 | #4.567-1 | abs(V′ − 1) ≤ C_{V′}ε′_k is #4.561.1-2's | The citation is now "(#4.561.1-2, #4.560.1-1)" |
| o4 | #4.568 | The list of ε′_k's constants omitted p₀, p₁, and β₀ | "(C_c, β₀ and CRE's in α̂_i, b_k's A₁ and M₀, and those of p₀ and p₁)" |

## Checks

- No duplicate tags. No CRLF.
- Line lengths: #4.52-1-1 605, #4.52-1-1.1 533, #4.52-1-2 231, #4.567-1 468, and #4.568 541 characters.
- #4.53-1.1-1 cites #4.52-1-2 for "MU^B satisfies #4.52-1-1's conditions"; the added clause supplies the levels #4.53-1.0-1 needs.

## Rounds

- 13a2 r12 (focused) is next. Its extract #4.52-1–#4.52-1.1 contains these repairs of #4.52-1-1.1 and #4.52-1-2. The spec is refreshed to this LF.
- Then 13b r12 (narrow: #4.52-1-1.1, #4.52-1-2, #4.567-1, #4.568), then 12a r15 (full).

## Pre-check of lf-p13a2-20261108-r12 (focused)

- **Spec.** specs\spec_p13a2_r12.json at LF 185f6a82754a, prior r11. --check gives 0 conflicts (6 allowed). Built: 17,010 argument characters.
- **Changed tags since r11 (8), all under review:**
  - **#4.50-1.1.0-0:** r11's t1, "twice the larger of that section's two bounds". The two bounds are (π/8)dB₀c_tot(1/128)ε₁ and c_{A′}ε₁ (r11's re-derivation).
  - **#4.51-2-1:** r11's t2, the tangency (VAR (98), (101), checked at p.293) and the ODE argument.
  - **#4.52-1-1:** r11's m1 and t3, the reading labelled "inferred, not printed", and U_0 restricted to Λ.
  - **#4.52-1-1.1:** the evidence, with 13b r11's m1 bridge and o1. CRE (1.3) and p.257 l.34, REG (1.15) at p.078 l.29–38, and REG (1.65) at p.087 l.36–44 are checked against the transcriptions.
  - **#4.52-1-2:** 13b r11's o2. The levels inside Λ are all shared, since Λ lies in the top layer (#4.44-0.2) and Ω^B_{m+1} = Ω^A_m (#4.5-2).
  - **#4.53:** r11's t3, "the element, unique on Λ".
  - **#4.53-1.0:** r11's t4, (52) at every level m ≤ k. a_k²abs(F) ≤ 2C₀^{ms}ε₁ gives abs(W(∂p) − 1) ≤ 2C₀^{ms}ε₁(ε/a_k)² ≤ 2C₀^{ms}ε₁(ε/a_m)².
  - **#4.55-1-1:** r11's t5, the prefactors at both exponents.
- No new symbol. No known weak point and no OPEN is in these lines.

## SHAs

LF 355391e734a7 → 185f6a82754a.
