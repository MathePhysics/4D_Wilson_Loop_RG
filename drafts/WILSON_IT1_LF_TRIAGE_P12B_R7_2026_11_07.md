# Triage of p12b r7 (lf-p12b-20261106-r7, 7 Nov 2026)

**Verdict.** Not clean: no fatal or serious findings, one minor (m1), and three trivia (t1–t3). The referee rates the rewritten #3.84–#3.87 correct, apart from m1, and confirms that every r6 finding (M1, t1, t2) is repaired. The clean count stays at 0, so r8 is again a full round.

## Repairs

| Finding | Words at stake | Repair (in place) |
|---|---|---|
| m1, #3.86-1 | "This is the bound of CRE p.266 l.12–13" | The print there is the R_k-free 30d²L²B₃(1 + β₀)ε_k; mine is (π/2)(11d²α₀ + 2α₁). New #3.86-1.1, split off for length: the bound "plays the role of" Bałaban's, is at most O(MR_k) times it through α₁, and e^{−δ2M₂R_k} absorbs the factor (#3.87). I had written the old sentence without opening p.266. |
| t1, #3.79 and #3.84-1.2 | "R_k^{−α₀}"; "α₀ (#T3.9) equal to" | #3.79 now reads "the small negative power of R_k there". #3.84-1.2 now names REG's α₀ of (1.7) (p.77) and states once that this α₀ and #3.86.1's α₁ (REG's of (1.35)) are local to #3.84-1.2–#3.87, not those of #T3.9 and #T3.12. |
| t2, #3.82-1 and #3.82-2 | the list "enter only … at these bounds" | Added p.364 (1.31), which is quadratic in ε_k and used against L^{−4N} (corrected file l.12; the raw print also has M^{14}). #3.82-2 now says "quadratic at pp.364 and 366" and "(1 + 2κ_s)² at pp.364 and 366". |
| t3, #3.70-3 | "which the same ratio absorbs" | Now: the quotient α_{0,m}/ε_m, unbounded as γ → 0 (#3.70-2), absorbs the factor here too, where the needed ratio is O(B₃)·6(1 + 2κ_s). |
| own find, #3.86-1 | "local by p.80 l.3–4" | The locality sentence is at REG p.80 file lines 5–6 (the referee quotes it there); the pin is now l.5–6. |

**Non-findings.**
- **#3.88's 2τ, repaired anyway.** I first left it, since (3.8) prints 2/10. When the user asked "Are you sure?", I counted it from REG (1.43) (p.83): P and S each hold two factors U₁(b) with |U₁(b) − 1| ≤ τε_kη, and Q is unitary. So |P||Q| + |S| ≤ 4τε_kη, and the referee's direct count is right. #3.88 now derives 4τ. It keeps (3.8)'s second term, 2τε_kη²(1 + 4τε_k), for E₂, and #3.89 has (1 − 4τε_kη)^{−1}. The bound is still ≈ 1.35ε_kη² < 2ε_kη².
- #3.94-1's |Λ^{(k)}| is a valid, if generous, factor; left as it is.

## Pre-check of r8 (lf-p12b-20261106-r8)
- **Changed tags (gate).** 8: #3.70-3, #3.79, #3.82-2, #3.84-1.2, #3.86-1, #3.86-1.1, #3.88, and #3.89.
- **Changed lines.** I re-read every changed line (#3.70-3, #3.79, #3.82-1's p.364 entry, #3.82-2, #3.84-1.2, #3.86-1, and #3.86-1.1) against the print: CRE p.266 l.8–30, LFR II p.364 l.9–14 (raw and corrected), REG p.80, p.81 l.24, and p.87 l.36–44.
- **Consumers.** #3.87 cites #3.86-1 and #3.84-1.2, both kept.
- **Table.** No table row is restated; the p.364 entry cites #T3.27.
- **Line lengths.** All changed lines are ≤ 610 characters.
- **Definition check.** 0 conflicts.
- **Size.** 24,741 characters (r7: 24,140).
- **Pins.** LF 729e79f7ffc7 (labels df31e17c8e9c), table 1e392e405632. The intermediate builds at LF 486d27ef0762 and 353cc2dce19c were never launched and are removed.
- **Status.** Launched on the user's go (7 Nov).
