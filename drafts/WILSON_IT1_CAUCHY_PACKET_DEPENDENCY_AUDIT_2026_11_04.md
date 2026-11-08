# Dependency Audit of the Cauchy Note for LF Review Packets 10, 14, 15, 30–32, and 48–49

Scope: WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md at sha 5278a721a30b, and the Cauchy packets of WILSON_IT1_LF_PACKET_PLAN_2026_11_04.md. The note has no tags, so the audit works at its subsections, its italic sub-blocks, and its lines. A script located every citation, as "§n" or "l.N", from one packet's lines into another's, skipping citations of other notes. Each located citation was read and classed as a premise (a fact the citing step uses), a definition or notation, or a pointer (a remark saying where a result is used or supplied). Only premises fix the order. The note's head, §4, §6.1, §7, §11, and the constants and sources lists are not in these packets.

## 1. The Packets

| Packet | Lines | Size |
|---|---|---|
| 10 | §1 (l.43–50), §6.2 (l.279–308), §9 (l.432–547) | 43k |
| 14 | §10.1–§10.3 (l.548–673) | 29k |
| 15 | §10.4 (l.674–896) | 49k |
| 30–32 | §§2–3 (l.51–89), §5 (l.100–268) | 122k |
| 48 | §8.1–§8.2 (l.313–340) | 33k |
| 49 | §8.3–§8.8 (l.341–431) and §10.5 (l.897–908) | 63k |

§10.5 moves from packet 15 to packet 49. *What the Gaussian Depth Feeds (And What It Needs)* uses §5 ((5.1v), the pair line, the lift condition, the frozen-current split, and R-Δ^c for one term) and §8.1, §8.2, and §8.5 (the fluctuated block field, the complex lines t ↦ tA, and the marked-cluster bound). §8.3 (l.347), §8.6 (l.402), and §8.7 (l.414) use its depth sources. Its citations of §8.6 and §8.7 at l.902 and l.907 say where its sources are consumed. The exception is θ̃ ≥ L^{−(1−2ε₀)/3}, a choice of parameter. So §10.5 lies between §8.1–§8.2 and §8.3–§8.8.

## 2. Forward Premises

The order is 10, 14, 15, 30–32, 48, 49. These are the premises that a packet takes from a later one.

| Packet | Premise | Holder | Kind of cycle |
|---|---|---|---|
| 10 | §9.4 *The lower bound at U = 1.* (l.480): (B1), (B2), and (B4) of §10.1 | 14 | Layered: §10.1 cites §9 only for §9.2 (l.558) |
| 10 | §9.4 (l.488): (B2) of §10.1 and D_V*λ^B = 0 of *The Multipliers.* (§10.3) | 14 | Layered: *The Multipliers.* (l.586–608) uses §9.4's surjectivity of Q₁^{pl} and its lift constants, which l.480–482 give before l.488 |
| 10 | §9.7 (l.516): the Cauchy estimate of §10.3 | 14 | Layered: l.672 says §9.7 uses it; the estimate does not use §9.7's result |
| 10 | §9.4 (l.480): (ii) of *Identities.* and the tents of *Regularity of the Lifts.* in §10.4 | 15 | Layered: §10.4 cites §9.3, §9.4, and §9.8 for regularity and the lift, not §9.4's lower bound |
| 10 | §6.2 (l.281, l.290): the relative difference r_i of the step covariance, (10.6) (l.893) | 15 | None: §10.4 does not cite §6.2 |
| 10 | §9.8 (l.546): the lifted pairs of 𝐔 and 𝐔^v lie in one orbit (l.110) | 30–32 | Layered: §5 cites §9.8 for the moment's input C″_Π and the pair line's distance, which §9.8 derives without l.110 |
| 10 | §6.2 (l.290): p₀(g_i)² ≤ ℓ_K (§8.7); (l.307): the recursion of §8.3 inside s′_K | 49 | Layered: §8.2 uses §6.2's bound of the old pairs (l.305), which carry the deep terms (l.327), §8.4 and §8.6 its per-variable measure bound 8abs(δ_m) (l.351, l.373), and §8.7 the threshold of s′_K ≤ 1 and the term Kμ_K of s_K (l.414, l.426). §6.2 uses §8.3's recursion only to bound the small-field insertions inside s′_K (l.307). §8.7's p₀(g_i)² ≤ ℓ_K (l.290) is a choice of parameter |
| 30–32 | §5 (l.232, l.262): the domain count C_X | 49 (§8.5, l.363) | None: C_X is a combinatorial constant, finite for κ large |
| 30–32 | §5's *The lift gauges.* (l.183): "as for h at l.329" | 48 | Layered: l.329's bound on h comes from Proposition 9's axial transports and c_N of l.116, not from l.183 |
| 48 | §8.2 (l.329): the norm class, ℰ_j, and R-Δ^c at the radii r (§5) | 30–32 | Backward |

Packet 14 has no forward premise: its citations of §10.4 and §10.5 (l.584, l.657, l.672) are pointers. Packet 15's forward citations all lie in §10.5, which moves to packet 49. The citations of §8 in §§2–5 other than those above are definitions (the margin m_k of CRE (3.15), the cutoffs (3.16) and their shells in §8.2(b), and δ_K = 0) or pointers ("§8.2 takes", "§8.2 reads", "§8.2 bounds that case directly").

## 3. Consequence for the Plan

Each Cauchy packet is clean when it has two consecutive clean passes and every premise it lists, including the forward premises above, is clean in its current form. Packet 10 is therefore clean once packets 14, 15, 30–32, and 49 are, for the listed premises only. Packets 30–32 are clean once packets 48 and 49 are, for C_X and l.329's bound on h. Each spec lists these premises as context.
