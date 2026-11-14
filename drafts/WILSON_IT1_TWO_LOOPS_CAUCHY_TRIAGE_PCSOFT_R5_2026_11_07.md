# Triage of pc-soft r5 (7 Nov 2026)

Review: verification\isolated_reviewer\reviews\pc-soft-20261106-r5\review.md, read in full.

## Verdict

CLEAN, and a full round: no fatal, serious, or minor findings; five trivial points. This is the part's first clean round. The part is done after a second clean full round (r6).

The referee re-derived these and found them correct:
- the band X_x and its set Ω^d_n ∩ E_n, with the induction off Y^x and K inside the cut layers;
- τ^d ≤ (1+β₀)²L^{4N^b}τ^d(x) on X_x;
- the gauge t_x, REG Lemma 1 iterated with CMP98 (53), and the sum ≤ 9d²κ_x;
- the locality τ^x(c) ≤ (1+β₀)²L²τ^d(y);
- q^d ≤ O(d²δ₀^{−d})(1+β₀)⁴L^{34−28N^b} and a* ≤ (2B₃C^d + 1)s^X, uniformly in X, p, and k.

## Repairs

| Point | Where | Repair |
| --- | --- | --- |
| The collar's cube statement is on CRE p.256 l.60, not l.59 | #6.16.3-3-3 | The pin reads p.256 l.60. |
| REG's (1.24) in a neighbouring block outside Ω^d_{l+1} holds through the induction, unstated | #6.16.3-5-0-1-1 | The parenthesis reads "its (1.24) being t_x's gauge, or V^x_l = 1 in a block off Ω^d_{l+1}". |
| "within (190)'s ball" omitted Proposition 9's ε₁ | #6.16.3-5-1 | Proposition 9 is taken, as at LF #4.530, with its ε₁ the larger of ε^b_x and 18d²L²(B₃ε^D + s^X)/C₁. Then V₀ meets (7) at ε^b_x ≤ ε₁, the data's ratio V′ has |V′ − 1| ≤ 9d²L²(B₃ε^D + s^X) < C₁ε₁ and |B| < 2C₁ε₁ (VAR p.305 l.31–44), and ε₁ ≤ a₁ for g small. The first wording, "ε₁ := …", was refused by the build's definition check, as ε₁ is defined in the LF and table #T3.19–#T3.20, so the line names Proposition 9's own parameter instead. |
| p₁ is defined later in the sequence (LFR I p.183 l.2) | #167-1 | The line reads "p₁(·), used in CRE only there and undefined, is LFR I's (p.183 l.2) or a slip for q₁ (D2.7 15.7, READINGS R43)". p.183 l.2 was checked: p₁(g_j) = (log g_j^{−2})^{p₁}, with p₁ < p₀. |
| #910 instantiated CRE p.268 l.38's k + 1 and Ω_{k+1} silently, and K′ also named the constant max(8C′, C_K) | #910; #6.4, #8, #14, #138, #139; D2.7's (R-eval) block | #910 reads "CRE p.268 l.38's regularity at its k + 1 = K′, … on the soft tests' support in its Ω_{k+1}". The constant C_K′ is renamed C_K^α in the two-loops note's five lines and in D2.7's (R-eval) block (my line); C_K^α occurs nowhere else in the YM4 notes or the table. |

To stay within 25k, these deletions change no mathematics:
- #6.16.3-5-1-0 no longer restates #6.16.3-5-0-3's distance.
- #6.16.3-5-0-3 cites M₁ ≥ L by its table row alone.
- #6.16.1's gloss on κ_s^{LF} points to table #T3.34-1.
- #6.16.3-3's ε_0 parenthesis is shortened.
- #167-1's two clauses on scaling and p₁ are merged.
- #6.16's roadmap sentence is deleted.

## Pre-check

- Every changed line was re-read: #6.16, #6.16.1, #6.16.3-3, #6.16.3-3-3, #6.16.3-5-0-1-1, #6.16.3-5-0-3, #6.16.3-5-1, #6.16.3-5-1-0, #167-1, #910, and outside the packet #6.4, #8, #14, #138, #139.
- Every use of C_K′ was grepped across the two-loops note, the pair note, D2.7, D2.6, the map, the table, and the LF, and all were renamed.
- ε₁ is now cited as Proposition 9's parameter, not defined.
- CRE p.256 l.58–61, LFR I p.183 l.1–3, LF #3.99, and LF #4.530 were opened.
- Nothing consumed #6.16's roadmap sentence.
- #6.16.3-5-1-0 still gives m′ ∈ {m_y − 1, m_y, m_y + 1}, the blocks lying within 2√dL^{j^x}η of y by #6.16.3-5-0-3.
- The part's argument went from 24,988 to 24,747 characters.

## LF updates checked

- LF d88cc8494a30, then 6445940379fb: changes in #4.4, #4.43–#4.45, #4.48–#4.48.1, #4.52-1, #4.54, #4.473, #4.499, #4.504, #4.540.4, #4.558-1, and #4.560–#4.562.
- TL and PC cite none of them. Their only LF §4 range is #4.10–#4.10-1, and #4.530–#4.530-1 are unchanged.
- LF ce6207d4b3e5 (labels eb0744201b11): changes in #4.559-2, #4.560-0, #4.560-1, and #4.560-1.1–#4.560-1.3, none of them cited. The LF session's W1 concerns LFR II p.358's class of U_0's extension at complex backgrounds. TL's only use of p.358 is γ₀ of LFR II (1.7) (p.358 l.3–5), so it is unaffected.
- The four specs are re-pinned to ce6207d4b3e5, and r6 is rebuilt: 24,747 characters, 0 conflicts.

## SHAs

TL c1c2d0f2132e (labels b74c687b4bb8, 1099 tags); PC 04cd2db746a7; LF 6445940379fb (labels 4165c40cf19a); table 1e392e405632; D2.7 4070b2971733.

The specs for pc-rstep r29, pc-links-a r1, and pc-links-b r1 are re-pinned (0 conflicts each). spec_pc_soft_r6.json (full, prior r5) is built at reviews\pc-soft-20261107-r6: 24,747 characters, 35,333 bytes, 0 conflicts. It is not launched and waits for the user's go.
