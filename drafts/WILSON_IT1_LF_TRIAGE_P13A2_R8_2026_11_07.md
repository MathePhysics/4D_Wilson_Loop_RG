# Triage: LF part 13a2, round 8 (lf-p13a2-20261107-r8), 7 Nov 2026

## Verdict

Clean: no fatal, serious, or minor finding. There are two trivial findings (t1, t2). This is 13a2's first clean round since r7. r9 is a full round; if it is clean, part 13a2 is done.

LF reviewed at b4f32ca7849c (table 30aec4a3446b, LABELS 59a564066c7f, Cauchy e0c534fa3017). The referee confirmed the round-7 repairs (m1, t1, t2) and checked CMP 98 (52), Proposition 6, and (158)–(163) against the transcription.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| t1: one sentence of #4.50-1.1.0 uses α₀ for PBG's parameter and for CMP 98 (52)'s | #4.50-1.1.0, #4.53-1.0 | (52)'s constant is now {#D.α₀^CMP} α₀^{CMP} := 4C₀^{ms}ε₁, defined in #4.53-1.0. #4.50-1.1.0 names it by section: "its α₀ of (52) (that section's α₀^{CMP}, a fixed multiple of ε₁, not PBG's α₀) sufficiently small" |
| t2: the verification of (52) is compressed (the conversion to the scale m, the layer-k bound before a_m ≤ a_k is stated, and "<" against "≤") | #4.53-1, #4.53-1.0 | #4.53-1 states only that W satisfies (52) at the scale m. #4.53-1.0, after a_m ≤ a_k, gives a_k²abs(F) ≤ 2C₀^{ms}ε₁ for both bases (#4.48.0-0), so abs(W(∂p) − 1) ≤ ε²abs(F) ≤ 2C₀^{ms}ε₁(ε/a_m)² < α₀^{CMP}(ε/a_m)², which is (52) with η = ε/a_m |

## Re-derivation

- (52) reads abs(U(∂p) − 1) < α₀η², with η the fine spacing in coarse units (p.026 l.14). For the scale-m averages from T_ε, η = ε/a_m.
- F_p = (1/iε²)log W(∂p), so abs(W(∂p) − 1) ≤ ε²abs(F_p).
- On the layer k, a_k²abs(F) ≤ 2C₀^{ms}ε₁ (#4.48.0-0, for U_0 and for Ũ). With a_m ≤ a_k, ε²abs(F) ≤ 2C₀^{ms}ε₁(ε/a_m)².
- With α₀^{CMP} = 4C₀^{ms}ε₁ the inequality is strict, since ε₁ > 0.
- The smallness of α₀^{CMP} is a condition cε₁ ≤ c′ (#4.50-1.2). It is stated as a fixed multiple of ε₁ in #4.50-1.1.0, which names the section, so there is no forward tag citation.

## Pre-check for r9 (lf-p13a2-20261107-r9, full round)

Gate answers, all yes:
- The changed lines are re-derived, and their arithmetic and citations re-checked: #4.50-1.1.0 (592 characters), #4.53-1 (420), and #4.53-1.0 (362).
- The new symbol α₀^{CMP} is checked against the LF, the table, and the Cauchy note: there is no other use. There is no new claim.
- Wider implications: only #4.53-1/#4.53-1.0 and (T-Λ) use (52).
- Linear order is kept: 13a2, then 13b.
- spec_p13a2_r9.json is current (definition check: 0 conflicts). Relabelled at LF 9186fbbbf1be (table b9386336d887, LABELS 857f1538fd28, verified; LABELS has #D.α₀^CMP). The packet is built: argument 13,272 characters, 18 files frozen and matched to the live hashes.

## Repaired SHAs

LF b4f32ca7849c → 9186fbbbf1be.
