# LF Packets 9–53: Logical Dependency Audit

Scope: the open points of (LF-A) and (LF-W) after packets 1–8, on the LF at sha e07654f829bf (labels 204e81123884), and the packets of WILSON_IT1_LF_PACKET_PLAN_2026_11_04.md that review them. The old packets 9–28 are named "old n". Scripts located every use, inside a packet, of a block outside it: by tag, by italic heading name, and by line pin into the Cauchy and W-δ notes. In the block graph of §§1–5, a citation of a head counts as a citation of its whole subtree, by indentation. Each located use was read and classed as a premise (the citing statement needs the cited one), a definition, or a pointer (a delegation of a separate case, a "which X uses" remark, a method "as in", or a notation remark). Where a head's subtree is large, the reading fixed the sub-blocks that carry the cited fact. Heading names that occur twice were resolved by reading the context. The verdicts below come from that reading.

## Consequences

1. Premises without review. Six groups of blocks that packets 9–28 (and, for #0.1.9–#0.1.13, packets 1–8) use as premises are in no packet, or carry repairs that are unreviewed. They become packets ahead of their users (§1).
2. External premises. The Cauchy note's §§1–3, 5, and 10, and the W-δ note's §§7–8 and 10–12, are unreviewed in their current form. The Cauchy note's §§6, 8, and 9 carry unreviewed repairs. Packets 9–28 use all of them. They become packets placed before the LF group that uses them most (§2).
3. Premise order. Once each citation of a large head is resolved to the sub-blocks that carry the cited fact, and the pointers are removed, the block graph of §§4–5 is acyclic apart from seven cycles of two to four blocks. Each of those is layered at the statement level and lies inside one packet. The LF packets are cut along a topological order of that graph, so no LF packet uses a statement of a later one (§3).
4. No circular dependence. The remaining cycles are layered at the statement level, and the constants are chosen in an acyclic order (§4).
5. Pins. Seven pins into the Cauchy note's §10 were wrong and are repaired. Eleven pins in §5 are stale and are repaired in the pre-check of the §5 packet (§5).

The order is in the plan. It has 45 packets before the splits at sub-headings: 25 LF packets and 20 external ones.

## The Clean Count

A packet is clean when it has two consecutive clean passes and every premise listed in its spec is clean in its current form. A repair that changes the statement of a listed premise re-opens every clean packet that lists it. Within the LF, premises lie in the same or earlier packets, so a repair re-opens only later packets, except through the external notes (§2). Packets 1–8 list #0.1.9–#0.1.13 and #4.22–#4.24 (packet 4, through #4.444 and #4.445.3) and #4.447 (packet 4) as premises from now on, so a repair there re-opens them.

## 1. Premises Without Review

| Blocks | Status | Users | Placed in |
|---|---|---|---|
| #0.1.9–#0.1.13, the frame of (KW): the identity of the members on shared blocks, the response H₁B′, the unit change 2dL, the crossing count, the adjacent layers, and the representative of the orbit | derived, not reviewed; in no packet | #0.1.14 (packet 3) cites #0.1.13; #0.1.30 (packets 1, 4, and 8) and #A.9 (packets 1 and 6–8) cite #0.1.11 | packet 9 |
| §4(a) and §4(b) beyond #4.7–#4.21: #4.1–#4.6 and #4.22–#4.42 (M′, R₁ = 1, the profile, the kernel form of VAR Proposition 4, the result) | reviewed and repaired, the repairs unreviewed (#0.20.3) | old 9, 18, 19, 21, and 22; #4.444 and #4.445.3 (packet 4) | packet 11, as §4(a)–(b) whole |
| #1.2 and §3(d), #3.16–#3.100 | §3(d) reviewed and repaired, the repairs and its (R-s) checks unreviewed (#0.20.3); #1.2 in no packet | old 14, 18 (#4.291 names *The integration variables.*), 22 (#3.77, #3.80), and 23 (#4.460 names #3.70); §5 (#3.40, #3.70) | packet 12 |
| §4(c), #4.43–#4.55 | reviewed and repaired, the repairs unreviewed (#0.20.3) | old 11, 13, 16, and 21 (#4.51) | packet 13 |
| #4.454.38–#4.454.41 | in no packet | the end of old 22's argument | packet 44 |
| #4.666–#4.671 | in no packet | (e)'s changes to the Cauchy note's §8 | packet 52 |

#A.11, #A.11.7, and #A.11.8 lie in packet 5's range #A.11.1–#A.11.20 and are reviewed. #0.1.2–#0.1.8 state what #0.1 derives and are no one's premise.

## 2. External Premises

| Section | Status in its note | LF users (old packets) | Placed |
|---|---|---|---|
| Cauchy §1, §6.2 | §1 unreviewed; §6.2 repaired, the repairs unreviewed | §3(d), old 16 and 26 | packet 10, with Cauchy §9, before §4(a)–(b) |
| Cauchy §9 | repaired, the repairs unreviewed | §4(b), §4(c), old 11, 13, 15, 16, 18, 19, and 22 | packet 10, before §4(a)–(b) |
| Cauchy §10: the alignment, (10.6b), (10.6c), β_π ≡ 0, the J-term, Assembly through (10.5′), the lifts | unreviewed (#0.20.2) | old 10–14, 17, 19, 21, 25, 27, and 28 | packets 14–15, before the (6) group |
| W-δ §§7–8 and 10–12 | not reviewed in their current form | §4(b) (#4.24), old 12 (§11 (a)), 14, 15, 17–24, 26, and 27 | packets 18–29, after the (6) group, before the (3) group |
| Cauchy §§2–3 and §5: (5.1c), (5.1v), (R-Δ^c-T), ℰ_j, 𝒮_z | unreviewed | old 15, 16, 18, and 20–24 | packets 30–32, before the (3) group |
| Cauchy §8 | repaired, the repairs and the boundary-term additions unreviewed | §3(d) (§8.6's bounds of d), §4(c) (§8.7), old 13, 14, and 21–28 | packets 48–49, after the (3) group, before old 14 and the (10) group |

No order puts every external section before all its users. The Cauchy note's §8.6 uses (LF) for its coarse histories, and the W-δ note's constants line takes ε₀ < 1/125 from LF #4.425, #4.456, #4.521, and #4.553–#4.554. Each section is therefore placed before the LF group that uses it most, and the clean count above covers the rest. §3(d) uses only §8.6's bounds of d, which come from LFR II pp.356–358 and hold for any fixed M₀ and do not use (LF), so the two notes are layered there. The two notes cite their own sections densely in both directions (Cauchy §5 and §8, §5 and §10; W-δ §11 and §12). So the order inside each note is fixed by a dependency audit of that note, as here, before its first packet.

## 3. The Premise Order

With subtree semantics, the (3) group, the (6) group, and parts of §4(b) and (e) formed one strongly connected set of 142 blocks. The cause was a few heads whose subtrees reach far past the fact that their citers use. The reading resolved each such citation as follows.

- *The functions of the configurations.* (#4.209) heads the whole (3) group, #4.209–#4.555. #4.169 applies that argument to the localised terms 𝐂(X), so old 14 (#4.151–#4.169) follows the group. #4.454.13 cites #4.169 only to say that the joint line reads no age factor, so that citation is a scope remark.
- *The complex class.* (#4.556) contains its applications #4.566 and #4.569. Its citers (#4.116, #4.155, #4.281, #4.597, #4.608) use the general part #4.556–#4.565, #4.567, #4.568. #4.201's class clause uses #4.566, and #4.566 uses #4.201's real bound; both lie in packet 17.
- *The multipliers.* and *The alignment.* contain #4.73–#4.74, the pointwise forms derived in (ii). Their citers use the rest of those sections. #4.73 uses the pointwise current bounds of *The Current at the Multiscale Chain.* and goes to packet 40. #4.74 goes to packet 37.
- *The Fine Side at the Multiscale Chain.* (#4.313–#4.328). Its citers (#4.234, #4.244, #4.301, #4.306, #4.338, #4.360) use the flow, its weights, σ_c, and the lift step, #4.313–#4.322. #4.331 uses only the global lift, #4.313–#4.320. #4.321 uses *The Lift ι_Y.* (#4.329–#4.334), so the order is #4.313–#4.320, then #4.329–#4.334, then #4.321–#4.322. #4.325–#4.328 have no premise in the group. #4.313's mention of *The Lift ι_Y.* announces the next section.
- *The joint line.* (#4.301) uses *The cubes □₀ at Z.* (#4.411) for the distance ≥ 2MR_ka_k of the cubes from the cut, so it follows packet 36. #4.315 uses the joint line's factorisation through M. The joint line's closing remark on the size of 𝐒_c uses σ_c, so the two are layered within packet 37.
- *The inputs at the composites.* (#4.444) contains #4.445–#4.454.41 by indentation. #4.442 uses only how ι_Y acts on a composite (#4.446.5). #4.456 uses the distance 3Ma_n (#4.445.4) and the layer fact of #4.446. #4.520 takes n₀′ ≥ max(n₀″, n₀‴) + 1, after the thresholds of #4.446.4 and #4.447.
- *The Current at the Multiscale Chain.* (#4.335–#4.366) contains its complex-point blocks #4.364–#4.366. #4.73, #4.311, #4.448, #4.460, and #4.463 use the real current, #4.335–#4.363.
- The complex part (#4.503–#4.552). Citations of it from real-point blocks are of two kinds. The complex-point clauses (the fine side at complex points, the per-term lift at the callers' complex data, the lift condition at complex points, the data angles at complex points, the Two-Constants form of the ratio) are reviewed in packets 46–47. The real-point uses are premises. #4.454.16's factor 18 for U_{k,Λ} and U_1 reads *The steps.* (#4.536), *The decay.* (#4.537), and the plaquette part of *The conclusion.* (#4.540). #4.387 reads the decay and *□₀ ∩ Z* (#4.541). #4.323 reads the thresholds of the real current part (#4.363). So *The complex members through (1.57)–(1.58) about 𝐔.* (#4.533–#4.546) form packet 42, before the age factor. Their own citations of the per-term lift (#4.540–#4.540.3) are the complex lift half of *The conclusion.*, and *The steps.*' citation of #4.454 names the callers' complex points.
- #4.454.16 (packet 43) precedes #4.323–#4.324 (packet 45), which use its factor 18. #4.454.16's citations of #4.324 are notation.
- *At D(s).* (#4.454.22) and #4.438, which uses it "by the argument of", lie in packet 43.

The other uses that the reading classed as pointers are these: #4.454.10 → #4.596 (notation); #4.22 → #4.445.3 (a user of M′); #4.171 → *The step map.* (the identity for (g″)^{−2}(x) − g_k^{−2} follows from the definition of g″ and is restated in place); #4.234 → *The linear operators.* (a method); #4.473 and #4.499 → #4.454 (the users of the values μ); #4.473 → *The conditions.* (the user of μ_mem); #4.301, #4.216, #4.229, #4.261, #4.297, #4.363, and #4.388 → *The background entry U_{1,2}.* (the U_{1,2} case); #4.233 → #4.455 (the terms of E_o); the delegations to *The near domains at ∂Y_i*, *The old generations*, *Deep V(Y) in a Young Polymer*, *The complementary-weight parts*, *Complex Backgrounds*, and *The Creation Difference of 𝔹_k^{(n)}*; and 19r's *The decay*, which is the Cauchy note's §9.8.

The uses of constants are in an acyclic order of choice, and they place no premise. n₀ and n₀′ (#4.553–#4.554) are chosen after the constants of the constructions (#4.226, #4.323, #4.454.27). n₀′ ≥ n_A is imposed at #4.520 (#4.454.27, #4.459). #4.50 collects the smallness conditions on ε₁ where they arise. #3.24 uses the value β = 1/8. The base's μ_mem := 8B₃/C_mem has C_mem := 4O(1)(1 + β₀)²B₃(1 + C_m), a constant of d and L (#4.532), and the base's statements hold at every fixed μ. #4.22.2 states the order L, then K and M′, then M, then g.

The LF packets are cut along a topological order of the resulting graph, with the plan's earlier grouping as the tie-break. A check of every resolved use against the cut finds no use of a later packet.

## 4. Cycles

Seven cycles remain. Each lies inside one packet and is layered at the statement level.

- #4.446, #4.446.3, #4.447, and #4.456 (packet 45). #4.456's location of the points read in the composite's top layer uses #4.445.4's distance 3Ma_n and #4.447's identification of the composite over 𝒮_z. Its bound uses #4.446's fact that □₀ meets only the member's layers ≥ n − 1. #4.446's lift condition uses #4.456's location, and #4.447.2–#4.447.5's membership uses #4.446.
- #4.301, #4.315, #4.321, and #4.331 (packet 37), as in §3.
- #4.517 and #4.536 (packet 42). #4.517 cites #4.536 for the method of the identity theorem ("as in *The steps.*"). #4.536 cites #4.517 for the pointwise identity ∇_{W^u}(Ad(u)S) = Ad(u)∇_WS and the size of a_j|∇log u|. Neither uses the other's conclusion.
- #4.520 and #4.554, and #4.521, #4.521.5, and #4.553 (packet 47). #4.520 takes n₀′ ≥ n_A, and #4.554's n₀ follows the constants of the constructions. *The Ratio.* (#4.553) bounds r(Y) by a power of L^{−n} and cites #4.521 only for the value 1/64 of the radii r⁺ at complex points. #4.521 and #4.521.5 use that bound to fix n₀′. By (T-M₁), M₁ ≥ M₁^τ is a constant of d, L, and G, fixed before n₀, so the constant order is acyclic.
- #4.58 and #4.128 (packet 17). *The lifts and the chain rule.* (#4.58) derives ⟨ψ, G_A^{−1}E⟩ = β(ℒψ, 𝒜^B) for ψ ∈ ker Q^A, which #4.128 uses. #4.58's closing remark, that E₀ is all of E at equal twisted data, rests on #4.128's split E = E₀ + E_Ξ.
- #4.201 and #4.566 (packet 17), as in §3.
- #4.582, #4.585, and #4.589 (packet 51). *The Crossing.* (#4.582) covers the completions of *The Completions.* (#4.588) through their definition as pieces with localisation domains meeting Z. #4.585 and #4.589 use its crossing count.

The cycle of packets 1–8 through #4.22, #4.444, #4.445.3, #4.446, and #4.447 is layered in the same way: #4.444 uses #4.447 only through its identification of the composite as RG I's U_j(□₀) over 𝒮_z (RG I p.273 l.39–42, p.276 l.26–36, and the Cauchy note's §5), and #4.22's M′ is a lower bound of d, δ₀, and c₀(⅛), fixed before all of them.

## 5. Pins

Repaired in the LF:

- #4.131: the π-part at l.850–854 and the gauge-fixing part at l.784–828.
- #4.136: the bound |δr| ≤ c_{g6}τ̂𝔰 at l.828, and the bracket of 𝔠(ρ) at l.812.
- #4.141: l.828.
- #4.147: R_X at l.788.
- #4.284.16: |Cov_p| ≤ osc·osc at l.757.

The cause was a +10 shift of the Cauchy note's §10 after the pins were set, and two pins that had been read as tags. Every other pin into the Cauchy and W-δ notes outside §5 was read against its target and holds.

Stale, repaired in the pre-check of the §5 packet: the Cauchy pins at #5.1 (l.39, l.114), #5.3 (l.140), #5.4 (l.116), #5.6 (l.118), #5.8 (l.140), #5.18 (l.324, l.312), #5.21 (l.405, l.464), #5.38 (l.180), #5.45 (l.39), #5.63 (l.140), and #5.66 (l.140), all lines of the Cauchy note.
