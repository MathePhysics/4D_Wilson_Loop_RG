# Part 12b (LF #3.63–#3.100-1), round 12, 9 Nov 2026

## Verdict

lf-p12b-20261109-r12 (full) has no fatal, serious, or minor finding, and one trivium. It is the second consecutive clean round, after r11 (full). So **part 12b is done**.

The referee checked every margin against the print. It re-derived (1.50)'s exact slack, the cascade removal, and the denominator average. It accepted the r11 handling of all six trivia, including the reason for keeping t2 (#3.70-5-1) as a labelled inference.

## Repairs

| Item | Finding | Repair |
|---|---|---|
| t1 (#3.77) | "through p₁ < p₀, γ small, and N large" omits the restriction that the first term of (1.94) needs: N ≤ O(1)(log g_k^{−2})^ν with ½ν ≤ p₀ − p₁ − 1 (p.198 l.55) | Reworded in place to "through N ≤ O(1)(log g_k^{−2})^ν with ½ν ≤ p₀ − p₁ − 1, γ small, and N large (p.198 l.49–57)". Re-derived: the first term of (1.94) is B₃(1 + β₀)N^{1/2}(A₁/A₀)(p₁(g_h)/p₀(g_h))ε_h ≤ O(1)(log g_h^{−2})^{ν/2 + p₁ − p₀}ε_h ≤ O(1)(log g_h^{−2})^{−1}ε_h, which is small for γ small. The second term is L^{−N}N^{1/2}O(1)B₃³B₅M⁶ε_h ≤ ½αε_h for N large. |
| remark (#3.97) | "at the soft test's threshold" is vacuous for the sharp second function of (1.28) | Reworded in place to "so for the soft tests they hold at the threshold t of #3.17". |

The referee's other two remarks need no change: #3.70-5-1's labelled inference, and the room at β = 1/8 in #3.79.

## Pre-check of the repair

- Line lengths: #3.77 is 578 characters, and #3.97 is 485.
- No consumer cites #3.77's wording.
- LF d598eaace460 → d72f4de24c38. The same edit pass also names the BP file at 40 LF lines that cited BP tags without naming the file; this is bookkeeping, and the SESSION_HANDOVER.md entry lists those lines.

Written 2026-11-09 04:07.
