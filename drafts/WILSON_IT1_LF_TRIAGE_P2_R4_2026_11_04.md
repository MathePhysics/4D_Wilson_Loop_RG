# LF Packet 2, Review 4: Triage

Review: verification\isolated_reviewer\reviews\lf-p2-20261104-r4\review.md (LF 60293c0941af). Verdict: every step labelled derived holds as stated, with no fatal or serious item; r3's S1 is resolved. This is the first of the two consecutive clean passes. All minors are accepted and applied.

## Minor

- **D1 (#0.1.18).** t and t₃ are now both capped below by ρ₀ and above by L, so t ≤ t₃ ≤ L holds by definition.
- **N1 (#0.1.26).** T^{−1}(1_{Q_R(y)}h₁) is now read on ℤ^d and truncated like φ and ψ₃. On the torus T annihilates the constant 1-forms. The cost is part of the tails.
- **K2-1 ((K2), #A.13).** The stale citation is replaced: for s < ρ₀, abs(u(b)) ≤ (E(Q_1(b))/a)^{1/2} ≤ (E(Q_{ρ₀}(b))/a)^{1/2}. For t(b) ≥ 4√dρ₀, *The massive case.* gives the sharper bound.
- **N2.** The bound now reads abs(∂₁φ) ≤ C(d)R² sup abs(σ), which also covers the truncation.
- **N3.** The P_N sentence now names both forms: P_N annihilates the functions supported in Λ^c, equivalently its range vanishes there.
- **N4.** "Lies in Λ^c" replaces "lies in one cell of Λ^c", in #0.1.26 and in (K2).

## Next

p2 r5 on LF 66596fa2e477 (labels 26aa1f7c94cf), as the second consecutive clean pass.
