# Packet 12a r3 Triage (LF #1.2, #3.16–#3.62-1)

## The Report of r3

r3 (lf-p12a-20261106-r3, launched 16:57 under .claude-Main) found no fatal finding, no serious finding, and three minor ones. All six second-round findings are repaired. So r3 is not clean, and r4 is a full round. Each finding was re-derived and repaired in place.

| Finding | Item | Repair |
|---|---|---|
| m1 | #3.40 | The second part was bounded per test. A cube at the scale j carries at most (n_T + 2)s_T(j) tests, each with N + 1 ≤ N̄(K − j) + 1 ≤ (2log g_j^{−2})^ν + 2, since N̄ is nondecreasing and k′ ≥ j; and s_T(j) ≤ 3 + (2log g_j^{−2})^ν (#CP.14). So the cube's second parts sum to ≤ (4C/κ_s)(n_T + 2)(3 + (2log g_j^{−2})^ν)²g_j²∣δ_j∣ ≤ ∣δ_j∣ for γ small (#3.40–#3.40-1). The bound is now at the scale j itself, without the passage to g_k. |
| m2 | #3.29, #3.30-1 | R_k = R̄(K − k), and R̄(n) is the smallest power of L that is ≥ 2(log(ḡ^{−2} + bn))^r, so R_k ≤ 2L(log(ḡ^{−2} + b(K − k)))^r ≤ 2^{r+1}L(log g_k^{−2})^r (#CP.13–#CP.14). With log g_k^{−2} ≤ 2log g_j^{−2} the factor of ε₁/δ′_j and of C_{1.27} is 2^{p₀+2r+1}, in place of 2^{p₀+r}. |
| m3 | #3.19.1-1 | A plaquette in several LM₂R_i-cubes is assigned to the first in a fixed order of the cubes. |

## Pre-check for r4

I re-read the changed lines #3.19.1-1, #3.29, #3.30-1, and #3.40–#3.40-1 and re-derived them.

- The bound N̄(K − j) ≤ (2log g_j^{−2})^ν + 1 is #CP.14. N = N̄(K − k′) ≤ N̄(K − j) holds because K − k′ ≤ K − j and N̄ is nondecreasing.
- (n_T + 2(N + 1))s_T(j) ≤ (n_T + 2)(N + 1)s_T(j) ≤ (n_T + 2)(3 + (2log g_j^{−2})^ν)².
- R̄(n) < L·2(log(ḡ^{−2} + bn))^r, since R̄ is the smallest power of L above that bound.
- No other line of the part uses 2^{p₀+r} or the removed bound N ≤ O(1)(log g_k^{−2})^ν.

The rest of the part is unchanged since r3's pre-check (WILSON_IT1_LF_TRIAGE_P12A_R2_2026_11_06.md).

#3.40 exceeded ~600 characters and was split into #3.40-1.

## Files

r3: LF ad44c62ee742, labels 2bcd7b0b486a, table 88a6dcbd277a. After the repairs: LF f4cbd0993021, labels a8a3625e1d03. r4 launches after 12b r2 has reported and been triaged.
