# Triage of lf-p13b2-20261108-r24

## Verdict

- r24 was a narrow round of 13b2 on r23's repairs, at LF 6ec2b60accc6, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** t1–t5, all citation or wording points.
- r23's m1 and t1–t4 were confirmed repaired. The referee re-read VAR p.280 l.51–52, (113)–(114), (173), REG p.88 and p.83, CMP98 (105)–(106), and LFR II (1.43)–(1.45) against the lines.
- The round is **clean**, so the count is 1. The next round, r25, is full.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1 | #4.517 | c^B(z) = U(V′V₀)^{u(z)} uses LFR I's orientation, which is VAR's u^{−1} | Added: "here in LFR I's orientation, VAR's u^{−1} (U₁ = U′^{u^{−1}}, p.281 l.3); inversion keeps R̄₀u^j = 1, by CMP98 (78) (derived), and abs(log u), so #4.517-0–#4.517-2 treat VAR's u" |
| t2 | #4.517-0 | "with the same u (REG p.88 l.9)": the sameness is Theorem 2's uniqueness | "which REG's Theorem 4 implies (REG p.88 l.9), with the same u by Theorem 2's uniqueness (REG p.83 l.18–20)" |
| t3 | #4.561-1-2 | "ε₀ + C₁ε₁ ≤ c₁ (#T11.25)": the row does not print c₁, which is REG's | "(VAR p.281 l.2, with REG Theorem 2's c₁, REG p.83 l.18–19)" |
| t4 | #4.561-1-2-1 | Proposition 6's inequality at the base 1 is not monotone, and its reason was unstated | "which holds since B₁ = 5dLB₀" |
| t5 | #4.561.1-1.2 | "B₅ LFR I's (#T1.4)" | "B₅ LFR I's (Proposition 1, p.194 l.43; #T11.29-0)" |

## Checks

- **t1.** In CMP98 (78), (R̄₀v)(y) = v(y)exp[iΣ_{x∈B(y)}L^{−d}(1/i)log w_x], with w_x := v(y)^{−1}R(V₀(Γ_{y,x}))v(x).
  - For v^{−1}, the argument is v(y)·w_x^{−1}·v(y)^{−1}, so its logarithm is −Ad(v(y))log w_x.
  - Hence (R̄₀v^{−1})(y) = v(y)^{−1}·v(y)exp(−m)v(y)^{−1} = ((R̄₀v)(y))^{−1}, with m the average of the log w_x. By induction the same holds for the k-th order averages.
  - abs(log u^{−1}) = abs(log u). #4.517-1-1's count uses only the norms of the factors' exponents.
  - VAR (16) and p.281 l.3 give U₁U₀ = (U′U₀)^{u^{−1}}. So with W^u(x,y) = u(x)W(x,y)u(y)^{−1} (#4.517-3), the note's u is VAR's u^{−1}.
- **t2.** REG p.83 l.17–20 (Theorem 2): "there exists exactly one gauge transformation u satisfying (1.29) and such that the conditions (1.36)–(1.39) hold for U₁ = U′^{u^{−1}}".
- **t3.** VAR p.281 l.2: "exactly for ε₀ + C₁ε₁ ≤ c₁"; REG p.83 l.18–19: "constants B₁, B₂(β₀), c₁ such that … α₀ + α₁ ≦ c₁".
- **t4.** 64ε₂^{AL} = 384B₁B₃C_{AL}ε′_k = 1920dLB₀B₃C_{AL}ε′_k ≥ 2B₀B₃C_{AL}ε′_k.
- **t5.** LFR I p.194 l.43: "|V_Λ(∂p′) − 1| < B₅M⁵ε for p′ ∈ Λ".
- **Line lengths.** #4.517 423, #4.517-0 199, #4.561.1-1.2 307, #4.561-1-2 469, #4.561-1-2-1 318 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r25 (full)

- **Spec.** specs\spec_p13b2_r25.json, prior r24, extracts as in r23 (#4.198-1 and #4.559–#4.560-0 as context).
- **Named steps.** Every tagged line of #4.517–#4.517-2, #4.561–#4.565-1, and #4.567–#4.568.
- **Permitted background.** It now also lists CMP98 (78), VAR (14), (18), and (114), and REG (1.29), (1.33)–(1.39), and Theorems 2 and 4.
- **Changed since r24.** #4.517, #4.517-0, #4.561.1-1.2, #4.561-1-2, and #4.561-1-2-1, each re-read in place.
- **Whole part.**
  - The part was read and re-derived line by line for r23 (WILSON_IT1_LF_TRIAGE_P13B2_R22_2026_11_08.md).
  - Since then, only r23's and r24's repair lines have changed. Each was re-derived against the print (WILSON_IT1_LF_TRIAGE_P13B2_R23_2026_11_08.md and the checks above).
  - The rest of the part is byte-identical to r23's snapshot outside these lines.
- **Symbols.** No new symbol. The definition check passed (0 conflicts, 7 allowed).
- **Size.** Built at LF a8968717c318: argument 24,485 characters (r24 24,279), 28 files.
- No known weak point and no OPEN is in the part.

## SHAs

LF 6ec2b60accc6 (r24's snapshot) → a8968717c318 (t1–t5). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).
