# Triage of lf-p13a2-20261108-r11

## Verdict

- r11 was a focused round of 13a2 at LF efa2e2fdb7b1, table 6d09b1b5054d, and labels 971e7d7d5325, with 13a1's #4.44-2 and #4.50-1.1.0-0.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1: the reading of LFR I's axial gauge in k-blocks was not labelled as a reading.
- **Trivial:** five, t1–t5.
- The round is not clean, so 13a2's clean count stays 0.
- Round 10's S1, m1, and t1–t5 were confirmed repaired. The referee checked S1's route in full:
  - the unique gauge-fixed element (REG p.079 l.16);
  - the lemma with d(L − 1) bonds and 2d + 1;
  - both brackets' W and V;
  - C′_Δ(M), c_{δD}, and their consumers.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.52-1-1, #4.561.1-1.3-1.0 | "Its conditions are REG (1.19) at the base 1" was presented as LFR I's definition, while LFR I never defines "axial gauge in k-blocks" (p.197 l.9) | #4.52-1-1 now reads "Its conditions are read as REG (1.19) at the base 1 (#T11.33; inferred, not printed, #4.52-1-1.1)". The new #4.52-1-1.1 gives the evidence: "LFR I does not define this gauge. The reading is supported by p.197 l.10, whose (1.65) [14] with the constant 11d² is REG (1.65) (p.087 l.36–44), REG's bound on the averages Ũ′^j of (1.19)–(1.20)." I checked REG p.087 l.36–44: the iteration of Lemma 1 on Ũ′^j gives 11d²α₀ + α₁ in (1.65). #4.561.1-1.3-1.0 now cites #4.52-1-1 instead of #T11.29-2, so the reading is stated once |
| t1 | #4.50-1.1.0-0 | The section has two bounds on a_ksup abs(A) | "twice the larger of that section's two bounds" |
| t2 | #4.51-2-1 | The ODE argument was compressed | "So H₁𝔛 is tangent to the critical set modulo REG (1.14) (VAR (98), (101)), and by ODE uniqueness, through a gauge lift, and the unique critical orbit of VAR Theorem 1, U^X_t is ...". I checked VAR p.293: (98) is the quadratic bound on δV/δA′, and (101) gives the equations after A′ = A₁ + H₁B |
| t3 | #4.52-1-1, #4.53 | The conditions are imposed inside Λ | "fix U_0 restricted to Λ" (written with a restriction bar in the note), and "the element, unique on Λ, in #4.52-1-1's gauge" |
| t4 | #4.53-1.0 | The recursion of #4.53-1.0-1 uses (52) at every level n ≤ k | "so at every level m ≤ k, as #4.53-1.0-1 uses, abs(W(∂p) − 1) ≤ ..." |
| t5 | #4.55-1-1 | The parenthesis named only the s = ⅓ prefactors | "(at s = ⅓ C_A(M) and #4.55-0.1's 2C(M)²(1 + β₀)², at s = 5/16 those of #4.568)". The duplicate "(s = ⅓ here, s = 5/16 in #4.568)" is deleted |

## Checks

- No duplicate tags. No CRLF.
- Line lengths: #4.50-1.1.0-0 387, #4.51-2-1 544, #4.52-1-1 605, #4.52-1-1.1 216, #4.53 520, #4.53-1.0 404, #4.55-1-1 552, and #4.561.1-1.3-1.0 434 characters.
- New tag: {#4.52-1-1.1}.
- #T11.29-2 is still cited by #4.52-1-1 for LFR I's print, and #4.561.1-1.2-1 cites it for (1.84). The table fork is asked to mark the reading in #T11.29-2 and #T11.33 as inferred, citing #4.52-1-1.1.

## Rounds

- 13b r11 (narrow) is next. Its extract #4.52-1–#4.52-1-2 contains #4.52-1-1.1.
- Then 13a2 r12, a focused round on these repairs.
- Then 12a r15 (full).

## Pre-check of lf-p13b-20261108-r11 (narrow)

- **Spec.** specs\spec_p13b_r11.json at LF 355391e734a7, prior r10. --check gives 0 conflicts (2 allowed). Built: 5,616 argument characters.
  - Under review: #4.52-1–#4.52-1-2, #4.556–#4.556-1, and #4.567–#4.568.
  - Context: #4.561.1-1.3-0 and #4.564–#4.565-1.
- **Changed tags since r10 (6), all under review:**
  - **#4.52-1-1:** 13b r10's m1, and 13a2 r11's m1 and t3, above. The pins LFR I p.197 l.3–4, l.9, l.10, REG p.079 l.16, and REG p.087 l.36–44 are checked against the transcriptions.
  - **#4.52-1-1.1:** the evidence for the reading. It is new.
  - **#4.52-1-2:** the run-B sentence, split off unchanged.
  - **#4.556-1:** the pointer to #4.5-2-1's {#D.Ũ} Ũ := MU^B, run B's configuration blocked to run A's lattice.
  - **#4.567-1:** the two radii, re-derived in WILSON_IT1_LF_TRIAGE_P13B_R10_2026_11_08.md (o3).
  - **#4.568:** the constants of ε′_k, checked against #4.560-0's ε′_k := ε_k + C_c(α̂₀ + α̂₁) + 25g_kb_k and #4.57's b_k := max(A₁p₁(g_k), M₀p₀(g_k)).
- **Outside the extracts.** #4.561.1-1.3-1.0's citation #T11.29-2 → #4.52-1-1 is bookkeeping. The next full round of 13b sees it.
- No known weak point and no OPEN is in these lines.

## SHAs

LF efa2e2fdb7b1 → 355391e734a7.
