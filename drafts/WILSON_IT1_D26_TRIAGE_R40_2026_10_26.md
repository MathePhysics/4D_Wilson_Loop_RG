# Round 40 Triage (15:10, 26 Oct 2026, date)

Two headless CLI referees (claude-opus-5-5, launcher verification\isolated_reviewer\run_app_review_cli.ps1, packets by build_round40_review_packets_20261026.py), launched 14:09 on the two derivations of WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md. Reviews: reviews\it1-d2-base-20261026-r1\review.md and reviews\it1-d2-rep-20261026-r1\review.md. Map at launch a021d5b39aaa; after this triage cce46318b239 (1614 lines, LF). V4 563736a8dfb9 at 14:41 (user-edited since the packets were built; cited by label).

## Open after this round

- **OPEN, D2.2(4)(d) for k ≥ 2: the representative of the ω-dependent factors.** v₁(x) = U_{k+1}(Γ^{(k)}_{y,x})^{−1}ρ̄_k(V_k)(Γ^{(k)}_{y,x}) (REG (1.19) with (1.20) telescoped). Missing: a k-uniform bound on the B′-variation of ρ̄_k(V_k)(Γ^{(k)}), the hierarchical transports of D(k)'s representative. What closes it: D(k)'s frame made explicit by the step-(k−1) map's output convention ((4)(c)); if that frame is axial relative to a V_k-dependent reference (VAR p.280: U_k(V) fixed in Ax_k(𝔅_k, U₀), U₀ = U_{k−1}(V₀), V₀ from (11) p.279), a bound on the B′-variation of Ū₀(V_k)(Γ^{(k)}), which the sources read do not give; then the multi-domain chains and the older-layer form C_wθ^{k−j−1}h_k for v₁.
- **Derived at k = 1, not reviewed:** v₁'s bound |log v₁(B′)| ≤ 4d(1 + o(1))sup_{B(y)}|𝐇₁| from RG1 (0.10) and the enclosed holonomies (gaps block, *The size bound* (d)), with two provisos on which axial gauge CRE p.248 and RG1 p.265 mean (single-contour vs mean-contour; both readings give a bound or make v₁ B′-independent).
- **Not re-reviewed:** the repairs of this round in map l.174, 194–196, 654–655, 869, 922, 970, 976, 981, 982, 988, 1418; the round-39 F-1–F-4 repairs in RC Pass 6 (f); map l.972 after round 38's n1, n2.

## (A) it1-d2-base-20261026-r1: the base points on Ω₁∖Ω₂

Verdict: FATAL (F1), with serious S1–S2 and minor M1–M8. Sound as written: the problem identification, the units, the layer-1 and layer-0 checks (after M1), the cube covering (after S2, M2), "rooted at k = 1", no dependence on D(1)(iii).

| Finding | Content | Disposition |
|---|---|---|
| F1 | "ε_n ≤ (1+β₀)²ε₁ by R-cpl₀" reverses R-cpl₀ (g_m ≤ (1+β₀)g_n for m ≤ n). CRE (2.8), p.256, read: ε_n ≤ (1+β₀)(n−m)^{1/2}ε_m and ε_m ≤ (1+β₀)²(n−m)^{β₀}ε_n for m < n. VAR (7) takes one ε for all layers, so ε^V_k = 2(1+β₀)max_{n≤k+1}ε_n grows like √k ε₁ and B₃ε^V_k < (1−β)α_{0,1} fails when g₁ ≪ g_K. | Accepted. The k-uniform claim withdrawn in map l.174, 976. The item is now derived at the root k = 1 only (layers 0–2, ε^V = 2(1+β₀)²ε₁ after M1); for k ≥ 2 the layer n = 1 is an older layer whose membership is the map's existing inheritance reading R-m (CRE p.277, l.921 *The real background*, Bałaban's), rooted here. The reviewer's repair sketch (localise Theorem 1 to layers 0–2 at general k with a lift and a (3.6)/(3.17)-type identity) is not adopted: the localised problem's inner data (the lift of V_n, n ≥ 3, or U_{k+1} on Ω₃) carry ε_n or the a priori ε^V_k, not O(ε₁); noted in l.976. |
| S1 | 𝐑-modified terms: the characteristic functions on the support may be those changed by the 𝐑-operation (p.258). | Accepted as a scope point. R-h (l.326–327): for k ≤ N the basic step of the R-operation acts on no component of the step map; at k = 1 none. 𝐑-modified terms belong to D2.7. Written into l.976. |
| S2 | "□̃¹ ⊄ Ω₂∖Ω₃" argued from the distance of Ω₂ to Ω₁ᶜ, which does not separate □̃¹ from Ω₃. | Accepted. At k = 1, Ω₃ = ∅ and the condition is trivial; the general-k fix Ω₃ ⊆ Λ₂ ⊆ Ω₂^{∼−2} ((3.5), (1.20)) recorded. |
| M1 | Mixed plaquettes at ∂Ω₁: δ(V̄₀V^{−1}) identifies V̄₀ with V, so χ₁ bounds them by 2ε₁; Prop. 2 on V₀ (2L²ε₀) not needed. | Applied; ε^V = 2(1+β₀)²ε₁, the L² dropped. |
| M2 | q₀ = p₀ branch constant. | Applied: C₀/A₀ ≥ 2L³(1+β₀)²B₃(CM/2 + 4R₁^VM₁)/(BCM) for (2.38)'s binding case; C₀/A₀ > 2(1+β₀)²B₃/(1−β) for (2.34). |
| M3 | dist(Ω₂, Ω₁ᶜ): cite Ω₂ ⊆ Λ₁ ⊆ Ω₁^{∼−2} ((1.20); p.251 Λ₁ = Ω₁^{∼−2}∩(R₁′^∼)ᶜ), not p.248. | Applied. |
| M4 | VAR's constant R₁ (p.277 (1)) clashes with CRE's scale R₁. | Applied: R₁^V throughout l.976. |
| M5 | V4 line pointers L429, L3977 stale. | Applied: cited by label (eq:native-source-explicit-outer-operation, the measurability paragraph of sec:branch-data, lem:c2-plaquette-deviation, (B1)(i), (B3)(i)). |
| M6 | The identification of U_{k+1} with the problem restricted to Ω₁^∼ is a reading, unlabelled. | Applied: reading R-reg (V4 (H4)) plus the criticality-and-uniqueness argument of V4 sec:c3-9-1 (prop:c3-9-1), written into l.976. |
| M7 | l.174 "CLOSED" inconsistent with "not reviewed". | Applied: l.174 reads "Derived at the root k = 1, reviewed (round 40), repairs not re-reviewed". |
| M8 | The layer-2 part of 𝒰₁'s domain at k ≥ 2. | Applied: at k = 1 it is Ω₂ (l.922's p.268 item); for k ≥ 2 inherited by R-m, written at the end of l.976. |

## (B) it1-d2-rep-20261026-r1: the representative and the frame of σ_j

Verdict: FATAL (F1), with serious S1–S2 and minor M1–M5. Sound as written: block locality of v₁; the reading of CMP 98 (64)–(77) apart from the identification of U₁; the geometric-sum arithmetic; the frame law of 𝐇^{(j)} and ‖Ad_g‖ ≤ e^{2c_G|log g|}; the 3S_H, 6S_H, 24 arithmetic; route (i) left open.

| Finding | Content | Disposition |
|---|---|---|
| F1 | U₁ = e^{iη𝐇_k(B′)} (Landau frame) in (77) computes the Landau-to-axial map ũ = R(U₀Γ)^{−1}(u_k(y)^{−1})u_k, not v₁. (I1): REG (1.19) is equivalent to the hierarchical transports agreeing, Ū^n(Γ) = Ū₀^n(Γ) at every level (recursion r(x_n) = Ū₀^n(Γ)^{−1}r(x_{n+1})Ū^n(Γ)); so v₁(x) = U_{k+1}(Γ^{(k)}_{y,x})^{−1}ρ̄_k(V)(Γ^{(k)}_{y,x}), whose B′-variation is that of D(k)'s representative's hierarchical transports. For k ≥ 2 this needs a k-uniform bound on the B′-variation of Ū₀(V)(Γ^{(k)}) for VAR p.280's reference U₀ = U_{k−1}(V₀(V)), which depends on V_k, hence on B′. At k = 1, if D(1)'s representative is CRE p.248's axial configuration U(y,x) = 1, v₁ = U₂(Γ_{y,x})^{−1}, G-valued, B′-independent, covered by (6)(b7). | Accepted. The item reverts to OPEN for k ≥ 2 with the exact missing input (above). At k = 1, V4's U₁ is in the axial mean gauge (V4 (B1): the condition is posed on the mean contour variables of RG1 (0.11)), so ρ₁(Γ_{y,x}) ≠ 1 in general and v₁ is B′-dependent; derived (not reviewed) |log v₁(B′)| ≤ 4d(1 + o(1))sup_{B(y)}|𝐇₁| from the mean condition (0.10) (log ρ₁(Γ_{y,x}) is the mean of the logarithms of the holonomies around Γ_{y,x} ∪ (−Γ), Γ ∈ 𝐆(y,x), each of ≤ 2dL bonds) and the telescoped holonomy difference of e^{iη𝐇₁}U₂ and U₂. Provisos recorded in l.195: if p.248's condition is single-contour, the reviewer's (b7) case applies; if RG1's Ax₁ is the relative mean gauge, the same bound holds for the mean of the mismatches. Written into l.194–196, 654–655, 869, 1418. |
| S1 | (127)–(131) bound Ū̄₁^j, not Ũ₁^j ((97): Ũ₁^j = (Ū̄₁^j)^{v_j}); for ũ the constant is 6d, not 2d; (106) runs in the same order as (77), normalised by (81). | Applied in l.195 as the corrected statement about ũ; not used for v₁. |
| S2 | The frame discrepancy costs ∝ θ_b|𝐇^{(j)}(b)|/g_j, not |σ_j| (σ_j = 0 is a counterexample). Corrected: |σ_j′ − Ad_{w(b₋)}σ_j| ≤ 2θ_b(e^{4c_G|log w|} − 1)|𝐇^{(j)}(b)|/g_j ≤ 4(e^{4c_G|log w|} − 1)S_H/g_j, charged to the total-move cushion; the condition becomes 40C_H(α_{0,j+1} + α_{1,j+1})g_j^{−3/2}e^{−R_j} ≤ 1. | Applied in l.982 (24 → 40; condition Σ_m|log w_m| ≤ (log 2)/(4c_G)). |
| M1 | REG (1.14)'s residual transformations are u = 1 on 𝔅_k, not block-constant; for (6)(b7)'s u the discrepancy is a harmless real rotation. | Applied. |
| M2 | Ad-invariance of the real support holds for G-valued w only; for G^c-valued w the centre's displacement is l.961's term. | Applied. |
| M3 | The frames compose over steps: the cumulative Σ_m|log w_m| is the relevant size. | Applied: Σ_m C_wθ^{m−j−1}h_m ≤ C_wh_{j+1}/(1−θ) plus v₁'s shares. |
| M4 | Multi-domain chains and the older-layer form C_wθ^{k−j−1}h_k not addressed for v₁. | Recorded under the OPEN input (l.195 (d′)). |
| M5 | Labels at l.194, 654, 869, 982 and READINGS l.69 to revert to OPEN. | Applied (l.194, 654–655, 869, 982, 988, 1418; READINGS round-40 bullet). |

## Caution on the base review's repair sketch

The reviewer proposed closing the k-uniformity by localising Theorem 1 to layers 0–2 with a lift of the deeper data and a (3.6)/(3.17)-type identity, decay (190), R₂ ≥ (log g₂^{−2})^r. Not adopted: the localised problem must be posed with data on Ω₃ (the lift of V_n, n ≥ 3, or U_{k+1} itself), whose plaquette bounds are ε_n ~ √n ε₁ or the a priori ε^V_k, so hypothesis (7) again carries a k-dependent ε. The scale-separation reason one would want (a level-(k+1) correction has fine curvature ≲ hL^{−2(k+1)}, absorbed by the margin β2^{−k}α_{0,1}L^{−2}) is not written as a derivation; the map rests on R-m's inheritance for k ≥ 2 instead.

## Sources re-read for this triage

CRE p.248, p.251, p.256 ((2.8)–(2.12)), p.258 (𝐑 and the characteristic functions), p.277; VAR pp.279–280 (Theorem 1, (8)–(14), the reference U₀ = U_{k−1}(V₀)); RG1 p.253 ((0.6), (0.10)–(0.11)), p.265; REG p.79 ((1.14), (1.19)–(1.20)); V4 by label: sec:branch-data (the measurability paragraph, (B1), (B3)), eq:native-source-explicit-outer-operation, (H4), lem:c2-plaquette-deviation, sec:c3-9-1, prop:c3-9-1.

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.174, 176, 194–196, 654–655, 869, 922, 970, 976, 981, 982, 988, 1418 (a021d5b39aaa → cce46318b239).
- READINGS_RECHECK_2026_10_23.md: round-40 bullet after the closure bullet.
- WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md: status header and "Open after this pass" amended.
- SESSION_HANDOVER.md: entry appended.
- This file (new).
