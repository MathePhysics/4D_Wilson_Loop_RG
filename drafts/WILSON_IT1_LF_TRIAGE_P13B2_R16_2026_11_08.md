# Triage of lf-p13b2-20261108-r16

## Verdict

- r16 was a narrow round of 13b2 on the lines changed by r15's triage and their consumers, at LF 59a9b7a0e6ac, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m-a. #4.517's "abs(log u) ≤ 4c_Gdε₂ when 2dε₂ ≤ r_G" tacitly needs c_G ≥ about ½ (it is false at c_G = 0, the abelian case). It also uses r_G at the radius itself, with no margin.
- **Trivial:** o-b and o-c. **Housekeeping:** the table's #T12.9-1 (c_pl without L², "d̄^c") and LABELS.
- The round is not clean, so 13b2's count stays 0. r15's m1–m3 and o2–o6 were confirmed repaired, with #4.563-2.1's arithmetic and the T_{1.70} spacings re-derived by the referee.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m-a | #4.517, #4.561-1.2, #4.561-1-2, #4.561.1-1.3-1.1 | The bound needs c_G ≥ 1 and a margin inside r_G | #4.517: "so abs(log u) ≤ 4c_Gdε₂ when 2dε₂ ≤ min(¼, r_G/2) (table #T4.10), with c_G ≥ 1, as abs([X, Y]) ≤ 2 abs(X) abs(Y) in the operator norm allows: the exponents of the transported factors that fix u, along the contour and in the normalisation, then sum to s ≤ 2dε₂, inside the radius of the BCH series, whose sum, in 𝔤^c, is the principal logarithm, of norm ≤ −log(2 − e^s) ≤ 2s for s ≤ ¼". (T-c), #4.561-1-2 and #4.561.1-1.3-1.1 now carry 2dε₂ ≤ min(¼, r_G/2). The table's owner is asked to record c_G ≥ 1 in #T4.10 |
| o-b | #4.563-3-1 | "run B's of a_j/L" names run B's layer spacing, not its plaquette spacing | "run B's fine plaquettes on T_{1.70} among them" |
| o-c | #4.561.1 | V′V_{Λ^c} (joining) versus V′V₀ (product) | "; V′V₀ is a pointwise product, unlike #4.44's V′V_{Λ^c}, which joins data on Λ and on Λ^c." |

## Checks

- **m-a, re-derived.**
  - Let W be a product of exponentials whose exponents' norms sum to s. Then abs(W − 1) ≤ e^s − 1, so the logarithm series converges when e^s − 1 < 1, and abs(log W) ≤ −log(1 − abs(W − 1)) ≤ −log(2 − e^s).
  - At s = ¼ this is 0.334 ≤ ½ = 2s. The ratio −log(2 − e^s)/s increases in s, so abs(log W) ≤ 2s for s ≤ ¼. (Elementary bound; the numerical value at s = ¼ is only a check of it.)
  - For s < r_G the BCH series of the product converges in 𝔤^c and agrees with the principal logarithm near 1, so log u ∈ 𝔤^c.
  - With s ≤ 2dε₂ this gives abs(log u) ≤ 4dε₂ ≤ 4c_Gdε₂ for c_G ≥ 1. Taking c_G ≥ 1 only weakens the note's other c_G bounds (#4.198-0.1's 1 + 8c_Gd, #4.536's u″_k bound in table row 326, W-δ's conditions such as 8dc_Gα₁ ≤ log 2, which stay of the form cα ≤ c′).
  - At the base 1, ε₂^{AL} ≤ ε₂/4 keeps a factor-4 margin.
  - #4.561.1-1.3-2 still uses 4c_Gdε₂ ≤ 1 to get 8c_Gdε₂^{AL} ≤ ½.
- **Line lengths.** #4.561.1 350, #4.561-1.2 631, #4.561-1-2 619, #4.561.1-1.3-1.1 265 and #4.563-3-1 482 characters. #4.517 (§4(d)) stays long, as recorded in r15's triage. No CRLF.

## Pre-check of lf-p13a1-20261108-r12 (full)

- **Spec.** specs\spec_p13a1_r12.json, prior lf-p13a1-20261108-r11, the whole part #4.43–#4.50-2. --check gives 0 conflicts (7 allowed).
- **Reading.** I read the whole part, #4.43–#4.50-2 (LF lines 524–583), before this full round. No gap was found. I checked:
  - **#4.50-0.0's chain.** abs(V′^B₀(V′^A₀)^{−1} − 1) < 2O(1)B₅M⁶ε_k ≤ C_𝔛(M)ε_k ≤ ε₁ ≤ C₁′ε₁, by C(M) ≥ 8(1 + κ_s)C_𝔛(M) (#4.43-1.2) and C₁′ = 4c_tot(1/128)C₁ ≥ 104.
  - **The growth radius at ±𝔛** (#4.50-0).
  - **The support of 1 − ζ₀** at the distance ≥ 6MR_k from Λ (#4.44-0, #4.48-3.0.0–#4.48-3.0.1).
  - **The factor ≤ 2 at matched scales** (#4.50-1.1.1-1, #C5.7-3).
  - **The kernel radius ε₃.** abs(𝒜₁ + H₁Y)_∞ < B₀(3B₃ + 2dL)C₁′ε₁ (#4.47-0–#4.47-0-1).
- **Changed since r11:** #4.44, #4.44-2-1, #4.46-0, #4.47-0, #4.47-0-1, #4.50 and #4.50-0.0 (r11's t-i–t-v). This triage's repairs touch no line of 13a1. 13a1 cites neither #4.517 nor c_G.
- **Size.** Built at LF be1108eaf60a: argument 22,901 characters, the whole part under review.
- No known weak point and no OPEN is in these lines.

## Rounds

- 13a1: count 1. r12 (full) is next.
- 13b2: count 0. After 13a1 r12: r17 (narrow, on this triage's lines), then r18 (full).

## SHAs

LF 59a9b7a0e6ac (r16's snapshot) → be1108eaf60a (m-a, o-b, o-c). Table 6d09b1b5054d (unchanged).
