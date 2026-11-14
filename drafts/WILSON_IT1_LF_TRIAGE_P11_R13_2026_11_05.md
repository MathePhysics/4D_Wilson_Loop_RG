# Packet 11 r13 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r13/review.md (changed lines), on LF 81b55840acbd, labels d356d8f6cba2, and table ede3cd24c7da.

## Verdict

r13 has no fatal, serious, or minor finding, so it is **clean**. It resolves r12's m-1 and t-1 to t-5. Its trivials t-a to t-d are repaired below. r14 is the full round; packet 11 closes if r14 is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-a | #4.12-2-1 | Λ_k ⊂ Ω_k ⊂ Ω_{h+1} now cites CRE (3.20) and (2.1). The distance from Z″_{h+1} to Ω_{h+1} holds under either reading of the enlargement in LFR I (1.11) (#4.18-2-1-3-2). The bound now reads ≥ 2M₁, which the same line gives. |
| t-b | #4.12-2-2 | "as #4.172 states". |
| t-c | new #4.12-2-3, #4.12-2-4 | Both Ω are unions of M₁-cubes of T_{L^{−h}}. M₁ < M are powers of L, the partitions are compatible (CRE p.245 l.33–39), and the R_j are powers of L (CRE (2.5)). (2.14)'s 2M₁ margin is checked for both joins: LMR_{h+1} to ∂Ω″_{h+1} in 𝐁₁, 2LMR_{h+1} to ∂Ω″_h in 𝐁₂, and ≥ 5LMR_{h+1} − 2dM₁ to the boundaries off Z. |
| t-d | new #4.13-3 | 𝐁₁'s mixed ∂Z pairs in the layers j ≤ h − 1 are ≥ dist(S, Z^c) ≥ 2M₁ apart. The others are 𝐁″_k's layers at ∂Z, ≥ LM₁ (#4.18-2-2). |
| packaging | none | The #4.537 extract is in packet.json (argument character 75480), on the line after its header. The reviewer read the LF line itself, which is the same text. |

## Labelled dependences

The review lists #4.18-0–#4.18-0-2 and #4.41-1-3-2 as labelled. Both are derivations from quoted print (LFR I p.177 l.27–31, p.178 l.2–9, p.192 l.40; CRE p.255 l.2–3), not conditions. They stay as written.

## Pre-check

- **Sources quoted.**
  - CRE p.245 l.33–39: "M=L^m", "M_2=L^{m_2}, and M_1<M_2<M", "M_2=L^2M_1", "The above partitions have to be compatible".
  - CRE p.257 l.9–11: (2.14)'s hypotheses.
  - CRE p.256 l.58–63.
- **Arithmetic.** 5LMR_{h+1} − 2dM₁ ≥ 5L³M₁ − 2dM₁ ≥ 2M₁, by M > L²M₁, R ≥ 1, and L ≥ 12d + 6. LMR_{h+1} ≥ L³M₁ ≥ 2M₁. For j ≤ h − 1, L^{j+1−h} ≤ 1, and L^{j+1−h}M₁a_h = LM₁a_j.
- **Every use.** "> M₁ from S" in #4.14-0 and #4.14-2 still holds with ≥ 2M₁. No other line cites #4.172-1 for 𝐁₂'s domain.
- **Lines.** The new lines are 416, 391, and 477 characters long.

## Repaired files

LF 517f95e16693, labels 4891cd09b8c8 (multiply defined 101, CR 0), table ede3cd24c7da unchanged.
