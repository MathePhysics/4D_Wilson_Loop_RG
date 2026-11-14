# Triage of lf-p13a1-20261108-r11

## Verdict

- r11 was a narrow round of 13a1 on the lines changed since r10 and their consumers, at LF c178f72a210d, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none. **Trivial:** t-i–t-v.
- The round is clean, so 13a1's clean count is 1. A narrow round cannot be the second clean round, so a full r12 is needed.
- r10's m1 and t1–t5 were confirmed repaired. The referee also confirmed that #4.47's justification of c_K is exact: #4.9-2-2 counts with α = ½ and takes the crossing decay from (2.58) at α = ½.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t-i | #4.44 | Bałaban gives abs(∂V_k − 1) < a₁ as an example | "(e.g. abs(∂V_k − 1) < a₁ on Z, p.194 l.32)" |
| t-ii | #4.46-0 | (103)'s ε₃ | "its ε₃ is VAR's of (77), fixed by (114), not #4.47-0's" |
| t-iii | #4.47-0 | "not a function of the dimension N" read as a dependence claim | "C_N #4.33's constant of 𝒩 (the subscript is not the dimension N)". #4.47-0 reached 637 characters, so its second half moves to the new #4.47-0-1 ("ε₃ bounds 𝒜₁ + H₁Y …"). ε₃'s definition stays in #4.47-0 |
| t-iv | #4.50, new #4.50-0.0 | "with B′ in 𝔤" not printed in (172) | "…writes such a G-valued datum as e^{iB′}, VAR's B′ of (172), with abs(B′) < 2C₁′ε₁, for ε₁ small, part of (T-Λ) (#4.50-1), B′ being 𝔤-valued as Sect. G's variable B = (1/i)log V′ (p.305 l.11–12; inferred, not printed in (172)). Bałaban's logarithm returns B′ there, since abs(B′) < π, so 𝔛 = B′." The sentence moves to the new #4.50-0.0, and #4.44-2-1 now cites #4.50-0.0 |
| t-v | #4.50-0.0 | B′ is also LFR II's fluctuation variable and #4.530's B′ | Named "VAR's B′ of (172)". A fresh letter B would clash with the shared datum B of exp(ig_kB) |

## Checks

- **t-iv.** VAR p.305 l.10–12 prints: "if V = V′V₀, V′ small, … then it is an analytic function of B = 1/i log V′". So Sect. G's variable is the logarithm of V′, which is 𝔤-valued for V′ ∈ G near 1. (172) at l.31–36 is checked against the transcript. For hermitian B′ with abs(B′) < π, CMP98 (22)–(23)'s logarithm (#T11.26) returns iB′.
- **Consumers.** #4.50-0 still cites "#4.50" for ‖𝔛‖_∞ ≤ C_𝔛(M)ε_k, which stays in #4.50. #4.44-2 cites #4.44-2-1, and #4.44-2-1 cites #4.50-0.0.
- **Line lengths.** #4.44 540, #4.44-2-1 313, #4.46-0 557, #4.47-0 296, #4.47-0-1 352, #4.50 404, and #4.50-0.0 482 characters. No CRLF. The new tags #4.47-0-1 and #4.50-0.0 were unused.

## Pre-check of lf-p13b2-20261108-r16 (narrow)

- **Spec.** specs\spec_p13b2_r16.json, prior lf-p13b2-20261108-r15.
  - Extracts: #4.198-1 and #4.517 (context), #4.559–#4.560-0 (context), #4.561–#4.565-1, and #4.567–#4.568.
  - Named steps: the 15 lines changed by r15's triage, with the consumers #4.561.1-0, #4.563-2.2, #4.567-1 and #4.568.
  - --check gives 0 conflicts (6 allowed). c_pl is allowed against table row #T12.9-1, which still states the earlier value. The spec says so, and the row is with the table's owner.
- **Re-read.** I re-read every changed line: #4.517, #4.561.1, #4.561.1-0.0, #4.561.1-1.3-1.1, #4.561-1, #4.561-1-2, #4.561-1.2, #4.563-2, #4.563-2.1, #4.563-2.1-1, #4.563-3, #4.563-3-1, #4.564, #4.565-1, #4.567 and #4.567-0.
  - **#4.561-1-2.** ε₂^{AL} ≤ ε₂/4 gives 16c_Gdε₂^{AL} ≤ 4c_Gdε₂ ≤ 1 and 2dε₂^{AL} ≤ ½dε₂ ≤ r_G, so #4.561.1-1.3-1.1's use of #4.517 at ε₂^{AL} meets both conditions.
  - **#4.561.1-0.0.** It is unchanged in content: the split moved c_av's definition, and #4.561.1-0 still reads c_av from it.
  - **#4.564.** Its pointers match the lines: #4.565-1 and #4.566 use the Lemma, #4.567 Cauchy's estimate, and #4.568 the absorption.
  - **#4.563-3-1, reworded in this pass.** The count now covers plaquettes of any finer spacing a, not only run B's on T_{1.70}: "their number (a_j/a)^d cancelling the factor (a/a_j)^d of their terms a^{d−4}abs(X − 1)² ≤ a^d abs(F)²".
  - **The term bound.** −½tr((X − 1)²X^{−1}) has modulus ≤ ½ abs(X − 1)² abs(X^{−1}) ≤ abs(X − 1)² for abs(X − 1) ≤ ½, since abs(X^{−1}) ≤ 2 there.
  - **c_pl.** abs(YU^r(∂p) − 1) ≤ abs(Y) abs(U^r(∂p) − 1) + abs(Y − 1) ≤ 2·2C₀^{ms}ε₁′ + 3L²ε₂ in units of a_j^{−2}. This is c_plC₀^{ms}ε₁′.
- **Consumers.**
  - #4.198-1 uses c_pl, which is now larger. That only weakens its bound, and c_pl is a constant of L and M (C_L, ϰ_c there).
  - The table's #T12.9-1 (c_pl) is sent to the table's owner.
  - 13a1's repairs above touch no line of 13b2.
- **Size.** Built at LF 59a9b7a0e6ac: argument 22,108 characters, including the context lines.
- No known weak point and no OPEN is in these lines.

## Rounds

- 13a1: count 1 (r11). r12, full, follows 13b2 r16.
- 13b2: count 0. r16 (narrow) is next, then 13a1 r12 (full), then 13b2 r17 (full).

## SHAs

LF c178f72a210d (r11's snapshot) → 59a9b7a0e6ac (t-i–t-v; #4.563-3-1 in the r16 pre-check). Table 6d09b1b5054d (unchanged).
