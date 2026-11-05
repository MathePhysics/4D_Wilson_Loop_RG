# Triage of LF Packet 9, Review r1 (lf-p9-20261104-r1)

Review: verification\isolated_reviewer\reviews\lf-p9-20261104-r1\review.md (LF 1bbb59aef5be). There is no fatal finding. Every finding is accepted and repaired. The repaired LF is 844525635d69, with labels 5e5d941a3f78 and 102 multiply defined.

## Serious

| Item | Finding | Verdict | Repair |
|---|---|---|---|
| S1 | #0.1.12.1 runs the crossing count for C_H at (K0)'s rate δ without the kernel bound that this needs. | Accepted. | #0.1.12.1 now states that PRT2's count runs at Bałaban's rate δ_* (#4.20), with the factor C(L). It bounds only the sums inside δ_U and §4's residual, and not C_H. C_H is (K0)'s weighted bound (#0.1.27; (K0)(g) with W_ms at the interfaces, #A.11.42–#A.11.43). The readings at intermediate scales go through #0.1.28 and #A.11.43. #0.1.12 points to #0.1.12.1 for what the count bounds. |
| S2 | #0.1.11 item 6 and #A.11.1's parenthetical claim a global regular gauge with O(1)Mα₀. That gauge does not exist, the Δ′_π and Δ_π^{(2)} perturbations are omitted, and the weighted statement fails without a comparison of rates. | Accepted. | New blocks #A.11.1.1–#A.11.1.6. They compare point by point in VAR Theorem 1's gauge on the class cube about each point, with the cut-off U_□ in PBG (3.37)–(3.38) about 1, and no global gauge. Covariant members are defined by (P1)–(P3). #A.11.1.2 gives the flat weighted bound plus the unweighted δθ_B, which is the review's suggested route. #A.11.1.3 proves (P1)–(P3) for H and H₁, including Δ′_π, G (3.130), and Δ_π^{(2)}, G₁ (3.134)–(3.138). #A.11.1.4 does the same for A_N. #A.11.1.5 glues A_♮, since U is not scale-j regular on the finer layers. #A.11.1.6 fixes the order of constants. #0.1.11's last sentence, #A.11.1's parenthetical, and the factor in #0.1.8, #0.1.10, #0.1.12, and #0.1.42 now read C_H + δ_U, δ_U ≤ 1. |
| S3 | #0.1.13: the gauge of the members' representative is inconsistent with that of C_H. Its analyticity in the data is not shown, and the bound of the covariant members is asserted. | Accepted. | #0.1.13 now takes Bałaban's representative u_R = exp(iη𝓗(B))U_k, Proposition 9's Landau form relative to the base, which is analytic in B (VAR p.309 l.8–13). At real data it is a G-valued transform (VAR p.305 l.36–37; REG Theorem 2). The chain runs at u_R^{g_♮^{−1}}, with first-order part A_N or A_♮ and ‖Ad(g_♮)‖ ≤ 1 + C(L, M)ε₁ (#A.9.3–#A.9.6). The covariant members are bounded through that representative by #A.9.6. #0.1.11's first sentence states the same representative. |

## Minor

| Item | Finding | Verdict | Repair |
|---|---|---|---|
| m4 | "C_H = o(L)" is not sufficient, since the factor is quadratic in C_H. | Accepted. | #0.1.9, #0.1.10, and #0.1.12 now read C_H(1 + 2C(d)C_H) = o(L), which the polylogarithmic bound meets. |
| m5 | The sum over layers in #0.1.12 drops e^{−m₀}. | Accepted. | #0.1.12 has Σ_{m≥m₀}e^{−m} < 2e^{−m₀}, with the further factor e^{−m₀}, and the condition ¼αδ₀W ≥ log L + 1. |
| m6 | "Without B₀, C′_Λ^{(j)}, (3.132)" holds only for the leading constant. | Accepted. | #0.1.13 states it for C_H's leading constant C(d)(1 + log L)^p. These quantities enter (K0) only at the interfaces through PBG (3.133) in (s1) (#A.11.26), in terms that RM, chosen after L, absorbs (#A.11.23). |
| m7 | The response is H₁B with B the REG (1.31) field of V′, and not H₁B′. | Accepted. | #0.1.11 corrected. |
| m8 | "L enters at the transitions" is a reading and is not exclusive. | Accepted. | #0.1.11 reads "L enters, among other places, at the transitions". |
| m9 | The proviso of #0.1.9 is a hypothesis in the packet, and the minimality argument is the inclusion of admissible sets. | Accepted. | #0.1.9 cites #0.1.40 for the proviso and states the inclusion: the averages compose, so the old term's admissible set lies in c's and contains c. The r2 spec adds #0.1.40 as context. |
| m10 | The source of the prefactor (9/8)(1+β₀)² is not in the packet. | Accepted. | The r2 spec adds #0.1.6, the Cauchy note's l.148, and its l.116 as context. |

## Re-opened Premises

#0.1.8 and #0.1.42 changed: their factor now reads C_H + δ_U. Every clean packet that lists them is re-checked after packet 9 is clean, together with the callers of #0.1.9–#0.1.13 (packets 1, 3–8) and #A.9.6, which now uses the sup-to-sup bounds of #A.11.1.5. The Cauchy note's l.31 now states the same factor (packet 10, unreviewed).
