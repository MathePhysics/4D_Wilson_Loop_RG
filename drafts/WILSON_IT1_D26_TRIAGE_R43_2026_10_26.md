# Triage of Round 43 (18:27, 26 Oct 2026, date)

Review: verification\isolated_reviewer\reviews\it1-d2-rep-20261026-r4\review.md (77f8ab871aac, written 18:00; CLI run, claude-opus-5-5, effort high; packet 4db5a75b65a6; prior review it1-d2-rep-20261026-r3). The user: "Yes, run round 43 on (d′) Step 8 (the complex-background case of D2.2(4)(d), map l.196) through the CLI, with the round-42 review as the prior review."

**Open after this round: nothing is OPEN in D2.2(4)(d). The serious finding S1 is repaired in the map (Step 8 rewritten; (6)(b7) *G^c-valued u*; D(k)(iii) *The ω-clause at complex configurations*). Not reviewed: these repairs and the six minors applied below.**

## Verdict

- Fatal: none. Serious: S1. Minor: m1–m6.
- Step 8's operator bound, analyticity, and k-uniform cost of the complex conjugations: CORRECT, with m1's constant, on backgrounds in D(k)'s hierarchical mean gauge. The round-42 m1 was NOT CLOSED because of S1 and m3.
- Disclosure: context-exposed (AGENTS.md auto-loaded); all packet hashes matched; the referee did not open CRE pp.260–261, CMP 98 pp.24–25, 30–31, 33, 39, CRE pp.276–277.

## S1 and its repair

**Finding.** Step 8 took every configuration 𝐔 = e^{iηa′}U_{k+1} of D(k+1)(iii)'s polydisc to be in D(k)'s hierarchical mean gauge and asserted ρ_k(V^{(k)}) = 𝐔. That identity is the continuation of Step 7's identity in the block data and reaches only the frame family U_{k+1}(W_c). Counterexample (flat, abelian, inside the full k ≥ 2 domain): U_{k+1} = 1, a′ = iιH on every e₁-bond, H in a Cartan subalgebra; the hierarchical mean gauge fixing is g₀(x) = e^{−iιη(x−y)₁H}, so v₁(0)(x) = e^{iιη(x−y)₁H} ≠ 1 with phase about ι/2 at the edge of the block. The referee's corrected statement: v₁ = g₀(𝐔)^{−1}v̂₁ with v̂₁ obeying Step 8's bound and v̂₁(0) = 1; the B′-independent G^c-valued factor is not covered by l.642, l.961 or l.982, since (6)(b7) relies on R(u) being real orthogonal. The referee had no verified repair and named the candidate: restate D(k)(iii)'s ω-clause covariantly and extend (b7) to G^c-valued rotations.

**Repair written (map l.196 Step 8, l.869, l.314, l.194, l.642, l.641).** Two observations close it without a new condition.

1. The same situation already occurs at the real points of the polydisc other than its centre: a real 𝐔 = e^{iηa′}U_{k+1} with real a′ is neither the step's output at its own data nor in the frame, and there v₁(0) is a real B′-independent change of representative, which (6)(b7) absorbs because the real rotation R(c₀)^{−1} preserves the slot polydisc. At a general 𝐔 (real or complex) v₁ = c₀(𝐔)v̂₁, with Ū := ρ_k(M^k(𝐔)) the minimiser at 𝐔's averages (a member of the frame family, the data being complex), v̂₁ the frame family's v₁ at Ū (Step 8's bound), and c₀(𝐔) := 𝐔(Γ^{(k)})^{−1}Ū(Γ^{(k)}) a gauge transformation fixing the block variables, B′-independent, analytic in 𝐔, equal to 1 on the frame family, G-valued at real 𝐔, and equal to g₀(𝐔)^{−1} when 𝐔 is a gauge transform of Ū (the referee's case).
2. The ω-clause at a complex 𝐔 is the analytic continuation of the clause at the real points. Written covariantly, the clause at 𝐔 holds for the slot values σ with R(c₀(𝐔))σ in the polydisc around the real support. At real 𝐔 this is the present clause verbatim (real orthogonal rotation). (6)(b7)'s covariance holds for G^c-valued B′-independent u by analytic continuation (closed words are analytic in u, G is a totally real uniqueness set in G^c). With σ̂ := R(c₀(𝐔))σ as the analytic coordinate, D2.1(2)'s identity theorem runs jointly in (a′, σ̂) as before. No size condition on c₀ is used. The propagation (l.961) and the frame bookkeeping (l.982) are unchanged because the backgrounds at which D(k) is invoked at step k (ρ_k(V_k) at real or complexified data) lie in the frame family, where c₀ = 1 and ŵ = u_k^{−1}v̂₁ = w_tot.

The referee's propagation concern (the cost of order dα_{1,j} against the margin r_{ω,j}2^{−(k+1−j)}) does not arise in this form, since no cost is charged: the domain is rotated, not shrunk. Written into D(k)(iii) as a continuation of l.314 (no new line, so the map's own line references stand).

## Minor findings and dispositions

| Id | Finding | Disposition | Where |
|---|---|---|---|
| m1 | (ii)'s level-m imaginary-part bound had a false reason ((0.12)'s paths have L + 2Σ_ν(abs n_ν) bonds; an abelian example gives about 2.1Lιη at d = 4); the factor is about exp(4c_Gdι), still 1 + o(1) | Replaced by the printed route: CMP 98 (97), (131) over the real base with A = a′, phases of the double-bar averages below 2ιL^{m−k}, of v_m at most dL^{m−k}ι; telescoped: Im Z(P_n) at most 2dιL^{n−k}, Im Z(T_b) at most 2dιL^{n+1−k}; factor exp(4c_Gdι(1 + o(1))) throughout (l.194, l.196, l.941); the R₀, R̄₀ inside (97)'s v_n and (126) named as o(1) contributions | map l.194, 196 |
| m2 | α₀ cited from l.319's 𝐉-radius; the l.972 analogy inapt (Prop. 3 there is for 𝐇^{(j)}, not u_k); the p.254 reading avoidable | α₀ now the curvature constant of (2.34) for 𝐔 in the full domain (l.313–314, k ≥ 2); the analogy dropped; the printed alternative (Ṿ = exp(iηA)U_{k+1}, A in 𝔤^c, Props 3–4 over the real base) recorded in the step, with what it still needs for the curvature of the averages | map l.196 |
| m3 | u_k's bound at complex 𝐔 is not carried by (4)(c) or (6)(e) (l.941 uses real transports) | Step 8 (iii) and l.941: the chain (106) has G^c-valued conjugations, each within (ii)'s bound, so C_w exp(4c_Gdι(1 + o(1))) = C_w(1 + o(1)) | map l.196, 941 |
| m4 | Citations in (0): D(k+1)(iii) not D(k)(iii); l.313 not l.319; l.1496's units; smallness of max α_{1,n} by g_n ≤ (1 + β₀)g_K (l.499, 982); l.503 is a condition, not a radius | All corrected in Step 8's opening | map l.196 |
| m5 | "Im log P" means X in Bałaban's convention; l.642 "this is" should be "at most" | Notation Z, Im Z for P = exp(iZ) introduced in Step 8 and used at l.642; "at most" written | map l.196, 642 |
| m6 | l.643 lacked the "not reviewed" qualifier; labels to be narrowed given S1 | l.643 qualified; labels at l.176, 194, 196, 216, 654, 869, 982, 1418 read "reviewed in rounds 40–43, the repairs after round 43 not reviewed" | map |

## Not re-reviewed

The round-43 repairs (Step 8 as rewritten, (6)(b7) *G^c-valued u*, D(k)(iii) *The ω-clause at complex configurations*, l.941's note); the round-42 and round-41 minors; the round-39 F-1–F-4 repairs in RC Pass 6 (f); map l.972 after round 38's n1, n2.

## Sources read for the triage

The review in full; the map l.313–314, 448, 636–643, 869, 941, 961, 972 (excerpts), 1496.

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.176, 194, 196 (Step 8 rewritten, (d′) heading), 216, 314, 641, 642, 643, 654, 869, 941, 982, 1418 (3fe708bf1a2b → b0c7573f2da6, 1614 lines, LF).
- READINGS_RECHECK_2026_10_23.md: l.72 (round-43 status, the repair, the reading in Step 8 (i)).
- WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md: status after round 43; "Open after round 43"; files changed.
- SESSION_HANDOVER.md: entry appended.
- This file (new).
