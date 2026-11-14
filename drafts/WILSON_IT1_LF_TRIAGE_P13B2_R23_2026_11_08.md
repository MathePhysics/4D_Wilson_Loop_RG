# Triage of lf-p13b2-20261108-r23

## Verdict

- r23 was the full round of 13b2, at LF 292b6345f662, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1, in #4.561-1-2 and #4.517-1. "At the base 1, ε₀ = 0" and "α₀ the base's regularity … and 0 at the base 1" misread VAR's ε₀ and REG's α₀. The conclusions survive.
- **Trivial:** t1–t4.
- The referee re-derived every other line of the part, including the full accounting of C_{V′}'s entries, the plaquette and density bounds, the Lemma's C_dc(M), and both coupling routes in #4.168's real form.
- The round is **not clean**, so the count returns to 0. The next round, r24, is narrow.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1(a) | #4.517-1 | REG's α₀ called the base's regularity, 0 at the base 1 | "That threshold is a smallness of α₀ + α₁, here VAR's ε₀ + C₁ε₁ (p.280 l.51–52), which (113) bounds by ε₂/B₁ (p.294 l.44)" |
| m1(b) | #4.561-1-2 | "At the base 1, ε₀ = 0" | "At the base 1, (173)'s ε₀ = B₃(1 + 4C_{AL})ε′_k (its term in (113)'s B₁(ε₀ + C₁ε₁), inferred, not printed) is ≤ the disc problem's B₃(1 + 4C_{V′})ε₁′"; the line was then 623 characters, so its last sentence became #4.561-1-2-1, and #4.561.1-1.3-1 now cites #4.561-1-2–#4.561-1-2-1 |
| t1 | #4.517-0 | "VAR Proposition 2 is REG's Theorem 4" | "VAR Proposition 2 applies REG's Theorem 2 (VAR's [6], p.280 l.51), which REG's Theorem 4 implies with the same u (REG p.88 l.9)"; the line was then 660 characters, so the CMP98 (106) sentence became #4.517-0-1 |
| t2 | #4.517-2 | "i𝔤^c" equals 𝔤^c | "places in 𝔤^c" |
| t3 | #4.517 | The appositive R̄₀u^j = 1 read as describing #4.536's u | Moved after "VAR Proposition 2 (p.281 l.1–3)"; "not #4.536's gauge factors u" now ends the sentence |
| t4 | #4.561.1-1.2 | The replacement of U, U′ by V_k(0), V^e(z) unstated for (1.43)–(1.45) | "By (1.43)–(1.45), with the same replacement" |

## Checks

- **m1, against the print.**
  - VAR p.280 l.51–52 sets α₀ = ε₀ and α₁ = C₁ε₁ for REG's Theorem 2 on the space (18).
  - VAR (113) (p.294 l.44) is B₃ε₁ ≤ ε₀ and B₁(ε₀ + C₁ε₁) ≤ ε₂. So ε₀ > 0 whenever ε₁ > 0, and α₀ + α₁ ≤ ε₂/B₁.
  - REG (1.71) holds "for α₀ + α₁ sufficiently small" (REG p.88 l.58), which is thus implied by the smallness of ε₂ already in (T-c) (#4.561-1.2).
  - (173) (VAR p.305 l.41) is ε₂ = B₁(B₃(1 + 4C₁)ε₁ + C₁ε₁) ≤ 6B₁B₃C₁ε₁. Matching it against (113)'s B₁(ε₀ + C₁ε₁) gives ε₀ = B₃(1 + 4C₁)ε₁. This is labelled inferred, not printed.
- **The base 1.**
  - B₁(B₃(1 + 4C_{AL}) + C_{AL})ε′_k ≤ 6B₁B₃C_{AL}ε′_k = ε₂^{AL}, for C_{AL} ≥ 1 and B₃ ≥ 1. So (113) holds there, and #4.517's argument runs at ε₂^{AL}, as #4.561.1-1.3-1.1 states.
  - B₃(1 + 4C_{AL})ε′_k ≤ B₃(1 + 4C_{V′})ε₁′ since C_{V′} ≥ 4C_{AL} and ε′_k ≤ ε₁′. So Proposition 2's ε₀ + C₁ε₁ ≤ c₁ at the base 1 is dominated by the disc problem's.
- **t1.** REG p.88 l.9 reads "Of course this theorem implies Theorem 2", and u is fixed by (1.29) in both.
- **Consumers.**
  - #4.517-1-1 (s_u ≤ 16dε₂) is unchanged.
  - #4.561.1-1.3-1.1 cites #4.517–#4.517-2 and #4.561-1-2 (for ε₂^{AL} ≤ ε₂/4, still in #4.561-1-2).
  - #4.561-1.2's "smallness of ε₂ in REG (1.71)" is right under the repaired reading.
  - The Cauchy note cites #4.517-0–#4.517-2 as a range (lines 633, 637, 1207), which now includes #4.517-0-1.
  - No live note cites #4.517-0 alone. The only LF citation of #4.561-1-2 that moved is #4.561.1-1.3-1's.
- **New tags.** #4.517-0-1 and #4.561-1-2-1 were unused before (Grep over the YM4 .md files).
- **Line lengths.** #4.517 248, #4.517-0 153, #4.517-0-1 531, #4.517-1 568, #4.517-2 377, #4.561.1-1.2 276, #4.561-1-2 420, #4.561-1-2-1 288 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r24 (narrow)

- **Spec.** specs\spec_p13b2_r24.json, prior r23, extracts as in r23, with #4.567–#4.568 as context only.
- **Named steps.** The changed lines #4.517, #4.517-0, #4.517-0-1, #4.517-1, #4.517-2, #4.561.1-1.2, #4.561-1-2, #4.561-1-2-1, and #4.561.1-1.3-1, with their consumers #4.517-1-1, #4.561.1-1.3-1.1, and #4.561-1.2.
- **Changed since r23.** These lines, each re-read in place.
- **Cited displays re-read in the transcriptions.** VAR p.280 l.42–53 ((14)–(18) and the identification α₀ = ε₀, α₁ = C₁ε₁); p.281 l.1–19 (Proposition 2's u and ε₂ ≥ B₁(ε₀ + C₁ε₁)); p.294 l.42–49 ((113)); p.305 l.31–54 ((172)–(175)); REG p.88 (Theorem 4, (1.67)–(1.73)).
- **Symbols.** No new symbol. The definition check passed in the build.
- **Size.** Built at LF 6ec2b60accc6: argument 24,279 characters (r23 23,895), 28 files.
- No known weak point and no OPEN is in the part.

## SHAs

LF 292b6345f662 (r23's snapshot) → 6ec2b60accc6 (m1, t1–t4, two splits). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).
