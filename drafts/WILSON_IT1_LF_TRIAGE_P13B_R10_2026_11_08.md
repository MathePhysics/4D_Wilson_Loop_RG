# Triage of lf-p13b-20261108-r10

## Verdict

- r10 was a narrow round of 13b at LF d9e8d74b97a1, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.52-1–#4.52-1-1, #4.556–#4.558-1.1, #4.561-1–#4.561-2, #4.563–#4.565-1, and #4.567–#4.568.
- **Fatal:** none. **Serious:** none.
- **Minor:** two. m1 is REG (1.14) read as a gauge condition in #4.52-1-1. m2 is #4.556-1's pointer, which points to a use of Ũ(z), not its definition.
- **Observations:** four, o1–o4.
- The round is not clean, so 13b's clean count stays 0.
- Round 9's m1, m2, o2, o5, and o6 were confirmed repaired, and o3 partly (see m2).
- The referee also searched for any use of Proposition 9 at a base regular with 2ε₁′ on the disc, or at the segment's data at complex z, and found none. The disc uses are all at z = 0, regular with ε₁′: #4.198-0, #4.506, #4.508, #4.512, #4.563-1.2, and #4.563-2.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.52-1-1 | "whose conditions are REG (1.19) at the base 1: u = 1 at the block points of the scale k (REG (1.14))" made the subgroup (1.14) a condition on U_0. (1.19) fixes an element in each orbit of that subgroup (REG p.079 l.16), and the freedom at the scale-k block points is fixed by V_Λ's axial gauge in Λ^{(k)} (LFR I p.197 l.3–4) | Rewritten in place: "V_Λ = M^k(U_0) being in the axial gauge in Λ^{(k)} (LFR I p.197 l.3–4, l.9). Its conditions are REG (1.19) at the base 1, which fix U_0 in its orbit under the transformations with u = 1 at the block points of the scale k (REG (1.14), p.079 l.16) ...". I checked both pins: p.197 l.3–4 reads "We fix for it the axial gauge in Λ^{(k)}", and l.9 reads "We take it in the axial gauge in k-blocks". REG p.079 l.16 (uncorrected file, the only one) reads "The conditions (1.19) determine uniquely an element in each orbit given by the subgroup (1.14)". The line would have been over 600 characters, so the run-B sentence is split off as #4.52-1-2, and #4.53-1.1-1 cites it |
| m2 | #4.556-1 | "(#4.504)" points to a use of Ũ(z). Its definition is {#D.Ũ} Ũ := MU^B at #4.5-2-1 | "at the reference Ũ(z), #4.5-2-1's Ũ = MU^B at the line's point z, as in #4.504" |
| o1 | #4.52-1-1 | The blocks are the order-k blocks, not B(y) = B¹(y) | "the corners y of the k-blocks" |
| o2 | #4.563-2 | U^r's 2C₀^{ms}ε₁′ is weakened to 4C₀^{ms}ε₁′ | No action. The slack is consistent and keeps c_pl unchanged |
| o3 | #4.567-1 | Measured in the exponent X of W_d, the radius is e^{−1/4}ρ_V | "≥ ½C_{V′}ε₁′ in abs(W_d − 1), and ≥ e^{−1/4}ρ_V in the exponent X of W_d = e^{iX}, by abs(e^{iX} − 1) ≤ abs(X)e^{abs(X)}". For abs(X) ≤ r := e^{−1/4}ρ_V ≤ ¼, abs(e^{iX} − 1) ≤ re^r ≤ ρ_V |
| o4 | #4.568 | The constants of ε′_k/g_k enter C_h only implicitly | "with the constants of ε′_k (C_c, CRE's in α̂_i, and b_k's A₁ and M₀)", from ε′_k := ε_k + C_c(α̂₀ + α̂₁) + 25g_kb_k (#4.560-0) and b_k := max(A₁p₁(g_k), M₀p₀(g_k)) (#4.57) |
| packet | spec | The spec placed CMP98 (2) at pp.19–21; it is on p.17 | The next specs cite p.017 |

## Checks

- No duplicate tags. No CRLF.
- Line lengths: #4.52-1-1 576, #4.52-1-2 174, #4.53-1.1-1 286, #4.556-1 323, #4.567-1 456, and #4.568 514 characters.
- New tag: {#4.52-1-2}. Its consumers: #4.53-1.1-1 cites it. #4.53-1.0-1 and #4.561.1-1.3-0 cite #4.52-1-1 for the conditions and the gauge, which stay there.
- #4.53-1.0-1's "u = 1 at the block points of the scale k" is the subgroup of (1.14) in which V^u is taken, which is consistent with the repaired reading.

## Rounds

- 13a2 r11 is next. Its extract #4.52-1–#4.52-1.1 contains #4.52-1-1 and #4.52-1-2, so it also reviews m1's repair.
- Then 13b r11 (narrow: #4.52-1-1, #4.52-1-2, #4.556-1, #4.567-1, #4.568), then 12a r15 (full).

## SHAs

LF d9e8d74b97a1 → efa2e2fdb7b1. Table 6d09b1b5054d (the fork's rows are pending).
