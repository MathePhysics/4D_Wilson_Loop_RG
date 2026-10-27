# Triage of Round 44 (19:12, 26 Oct 2026, date)

Review: verification\isolated_reviewer\reviews\it1-d2-rep-20261026-r5\review.md (264e9a693eff, 281 lines, written 18:59; CLI run, claude-opus-5-5, effort high; packet 8a80d43f9587, 312,488 bytes; prior review it1-d2-rep-20261026-r4). The user: "Yes, run round 44 on the round-43 repairs (map l.196 Step 8 as rewritten, l.314 the ω-clause at complex configurations, l.869 G^c-valued u, l.642, l.941) through the CLI, with the round-43 review as the prior review."

**Open after this round: nothing is OPEN in D2.2(4)(d). No fatal or serious finding. Eight minors, all repaired in the map; not re-reviewed.**

## Verdict

- Fatal: none. Serious: none. Minor: F1–F8.
- The repair is correct in mechanism: the factorisation v₁ = c₀(𝐔)v̂₁ is an identity; c₀ is B′-independent, analytic, 1 on the frame family, and G-valued at real points; (6)(b7)'s covariance extends to G^c-valued u by analytic continuation (G a maximal totally real submanifold of G^c); l.961 and l.982 are untouched because D(k+1) is consumed at step k+1 only at ρ_{k+1}(V_{k+1}), where c₀ = 1. Round 43's S1: closed in mechanism, closed once F1 and F2 are applied (both applied). Round 43's m1–m6: CLOSED (m1 with F4's constant, m2 with F8, m3 with F2's base, m6 except F7). Round 42's m1: closed subject to F1–F3 (applied).
- Round 43's propagation concern (a cost of order dα_{1,j} against r_{ω,j}2^{−(k+1−j)}) does not arise anywhere in the reviewed text once F2 is applied (Q4).
- Disclosure: context-exposed (AGENTS.md auto-loaded); all packet hashes matched; the referee opened no Bałaban page outside the packet; conclusions depending on material not supplied: PBG (3.33)–(3.34) (known through l.972's paraphrase), VAR p.309 and Prop. 9, CRE pp.276–277, D2.1(2) beyond l.448.

## Findings and dispositions

| Id | Finding | Disposition | Where |
|---|---|---|---|
| F1 | The covariant ω-clause rotates the wrong way: with Cov's word(𝐔^u, R(u)𝐉, σ) = word(𝐔, 𝐉, R(u)^{−1}σ) and Ax(𝐔) = Ax(Ū)^{c₀}, the clause at 𝐔 holds for σ with R(c₀)^{−1}σ in the polydisc, not R(c₀)σ; the same inversion in (b7)'s "R(u)σ"; with the printed σ̂ the identity theorem's left side is not known to be analytic | Checked independently (the transports of Ax(Ū)^{c₀} are 𝐔's; Cov as stated in (b7)). Corrected to R(c₀(𝐔))^{−1}σ, σ̂ := R(c₀(𝐔))^{−1}σ, and R(u)^{−1}σ in Step 8, l.194, l.314, l.869; l.314's premise restated (Ax_k at 𝐔 is Ax_k at Ū transformed by c₀); the biholomorphic change (a′, σ̂) ↦ (a′, R(c₀(a′))σ̂) noted in Step 8 | map l.194, 196, 314, 869 |
| F2 | ŵ := u_k^{−1}v̂₁ does not separate c₀ correctly: w_tot = u_k^{−1}c₀v̂₁ has c₀ in the middle; the absorbed factor must be outermost, w_tot = c₀(c₀^{−1}u_kc₀)^{−1}v̂₁, which is c₀û_k^{−1}v̂₁ exactly when the Landau gauge at 𝐔 is posed relative to Ū^{c₀} (REG (1.18); PBG (3.33)–(3.34) as at l.972); posed relative to 𝐔 itself, 𝐇_k(𝐔, 0) ≠ 0 and a second B′-independent factor appears; the 𝐇_k of Steps 4–6 at a general 𝐔 must be Ū's | Written in Step 8: the step at 𝐔 is the c₀-conjugate of the step at Ū, since its words depend on 𝐔 through the block data and the hierarchical transports only, both shared with Ū^{c₀}; so the Landau gauge is posed relative to the minimiser Ū^{c₀}, 𝐇_k = Ad_{c₀}𝐇̂_k, u_k = c₀û_kc₀^{−1}, w_tot = c₀ŵ, ŵ := û_k^{−1}v̂₁ with 𝐇̂_k(0) = 0; l.641, l.642, l.194 adjusted | map l.194, 196, 641, 642 |
| F3 | Ū and family (I) are not field-small per bond in the mean frame (round 43's flat example: Ū = 𝐔^{g₀} has phase ι on the bonds between top blocks; l.972 says the complexified minimiser is only phase-small in axial-type frames); the stated source (VAR (172), CMP 98 Prop. 3) does not give O(ι) per bond; (ii) as written applies to field-small bases only; α₀ must be Ū's curvature | Written as *The reference Ū*: B′₀ := (1/i)log(M^k(𝐔)M^k(U_{k+1})^{−1}), of size O(dι) by (97), (131) over the real base and one more mean; Ū = Y^g with Y := e^{iη𝐇_k(B′₀)}U_{k+1} (Step 4 with B′₀) and g its mean gauge fixing (Step 7), log g of size O((C_w + 3d)dι); Y field-small over the real reference with ι₀ = O(dι), its curvature that of the Landau configurations ((6)(e) *The curvature conditions*, (4)(f)); (i)–(iii) at the base Y with α₀ Ū's curvature; Ū^n = (Y^n)^g, P_n(Ū) = g(y)P_n(Y)g(x_n)^{−1}, h_Γ(Ū^n) = Ad_gh_Γ(Y^n), ρ_k(V_k) = ((e^{iηX̂}Y)^g)^{ĝ} with X̂ = Ad_{g^{−1}}𝐇̂_k; every g-conjugation costs e^{O(c_G(C_w + 3d)dι)} = 1 + o(1). The analyticity of Ū cited from VAR p.307 on (172) (ε₁ enlarged as at l.972), CMP 98 Prop. 4 or RG1's averages for M^k(𝐔), and Step 7 | map l.194, 196 |
| F4 | The Result's factor undercounts: Step 3's P_n factor and Step 5 (α)'s T_b factor multiply, e^{8c_Gdι(1+o(1))}; at Ū times F3's factor; still 1 + o(1) | Written in the Result and at l.194; the smallness condition now c_G(C_w + 3d)d max_nα_{1,n} small | map l.194, 196 |
| F5 | Family (I) should be {ρ_k(V): V complexified level-k data}, so that Ū is in it; "no size condition on c₀" is too strong: the continuation needs c₀ in the connected domain of analyticity in u, which log c₀ of size O(dι) gives | Family (I) redefined; the size O(dι) of log c₀ derived (c₀ = [𝐔(Γ)^{−1}U_{k+1}(Γ)]·v₁(U_{k+1}; B′₀), the factors at most 2dι and at most 3d times the sup of 𝐇_k(B′₀)); "rotated, not shrunk" kept; the proviso also stated in (b7) | map l.196, 869 |
| F6 | (11)(c)(β), l.1498, applies D(k)(iii) at the polydisc points e^{iη(𝐇(s,tB′)+a″)}U_{k+1}, general complex configurations; read through the frame point: ŵ via (4)(c), c₀ into the covariant clause, never through (4)(c)'s budget | One sentence at l.1498 and a cross-reference in Step 8 | map l.196, 1498 |
| F7 | l.196's label "Step 8 reviewed in round 43, correct on the frame family" overstates: round 43 accepted field-small mean-gauge backgrounds | Label rewritten (bound at field-small backgrounds, round 43; factorisation and covariant clause, round 44) | map l.196 |
| F8 | The printed alternative does not need "(2.34) for 𝐔 through the relative averages": at a field-small base (iii)'s holonomy bound follows from (97), (131), and the real base's κ_n; complete modulo the real-base Prop. 2 | Rewritten in (i); the reading is used at the base Y of *The reference Ū* | map l.196 |

Residue noted by the referee and left: l.642 writes w = ∏e^{Z_j} without the i of P = e^{iZ} (harmless, the referee's words).

## Not re-reviewed

The round-44 minors F1–F8 (map l.194, 196 Step 8, 314, 641–643, 869, 1498); the round-42 and round-41 minors; the round-39 F-1–F-4 repairs in RC Pass 6 (f); map l.972 after round 38's n1, n2.

## Sources read for the triage

The review in full; the map l.194–196, 313–314, 641–643, 869, 942–943, 972 (excerpt), 1418 (excerpt), 1498; the review's conventions checked by hand (the gauge action, (U^b)^a = U^{ab}, the transports of Ax(Ū)^{c₀}, the order of the factors in w_tot, the conjugation identities (e^{iηX}Y)^g = e^{iηAd_gX}Y^g and U^{c₀û_k} = (U^{c₀})^{c₀û_kc₀^{−1}}).

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.176, 194, 196 (Step 8 and the (d′) heading), 216, 314, 641, 642, 643, 654, 869, 982, 1418, 1498 (b0c7573f2da6 → d115d7204a0e, 1614 lines, LF).
- READINGS_RECHECK_2026_10_23.md: l.72 (round-44 status, the eight minors, the pages).
- WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md: status after round 44; "Open after round 44"; files changed.
- SESSION_HANDOVER.md: entry appended.
- This file (new).
