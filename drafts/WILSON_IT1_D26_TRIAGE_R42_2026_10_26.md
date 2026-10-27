# Triage of Round 42 (17:38, 26 Oct 2026, date)

Review: verification\isolated_reviewer\reviews\it1-d2-rep-20261026-r3\review.md (70ee72c6c824, written 17:22; CLI run, claude-opus-5-5, effort high; packet fbf4c5117898; prior review it1-d2-rep-20261026-r2). The user: "Yes, run round 42 on the k ≥ 2 derivation of D2.2(4)(d) (map l.194 summary and l.196 (d′), Steps 1–7) through the CLI, with the round-41 representative review as the prior review."

**Open after this round: nothing is OPEN in D2.2(4)(d). Not reviewed: the complex-background step written in this triage ((d′) Step 8, map l.196) and the six minors applied below.**

## Verdict

- Fatal: none. Serious: none. Minor: m1–m6.
- Steps 1–6 of (d′): CORRECT. Step 7: CORRECT for the analyticity, v₁(0) = 1, the locality, the multi-domain and older-layer forms; its complex-background clause ("as for u_k") UNSUPPORTED as a derivation, a scope limit (m1).
- Every l.194 consequence CORRECT (the level-n mismatch bound at n = 0 is d(L−1)η, written in).
- All five round-41 OPEN items for k ≥ 2 CLOSED for G-valued U_{k+1}: the k-uniform bound on the B′-variation (2d(1 + o(1)) ≤ 3d), analyticity, the older-layer form (relative to R-bg), the multi-domain chains (CRE (3.10) at each earlier step), the gauge of the reference (hierarchical mean axial gauge; VAR p.280's U₀ not used).
- Disclosure: the referee was context-exposed through an auto-loaded AGENTS.md, read the prior review through Grep excerpts only, and found all packet hashes (23 Bałaban pages, the notes files, V4 563736a8dfb9) matching.

## Findings and dispositions

| Id | Finding | Disposition | Where |
|---|---|---|---|
| m1 | Complex backgrounds asserted "as for u_k" without derivation; the caller (map l.639–642) needs v₁ jointly analytic in complex backgrounds and a size bound with complex conjugating transports | Written as (d′) Step 8 (derived, not reviewed): the means and averages are defined on G^c (RG1 p.252 l.39–40, p.253 l.17 and l.36, (0.12)); CMP 98's Propositions 2 and 4 at G^c-valued configurations by RG1 p.254 l.8–10 (Bałaban's), with D(k)(iii)'s complex-domain constants; the conjugating transports P_n, T_b have imaginary logarithm at most dι(1 + o(1)), ι the per-bond radius of D(k)(iii)'s domain in units of the layer's scale, and the norm of Ad_P is at most exp(2c_G times the imaginary part of log P) (Hermitian-part bound); factor exp(2c_Gdι(1 + o(1))) = 1 + o(1), k-uniform; result 3d sup of the norm of 𝐇_k at real and complex backgrounds; l.194 summary and l.642's convention updated to Z_j in 𝔤^c with the Ad-norm factor | map l.194, 196, 641, 642 |
| m2 | Per-factor bound for v_n's means wrong (2dL^jηα₁ instead of d(L−1)L^jηα₁); conclusions stand | Corrected in Step 5 (α) ("a block path of at most d(L−1)/2 level-j bonds, each < 2α₁L^jη by (131)", total d(L^n − 1)ηα₁(1 + o(1)) ≤ dL^{n−k}α₁(1 + o(1))) and in the ũ bullet (d(L−1)L^jη) | map l.196 |
| m3 | Step 1's conditions hold on Γ_{n+1} = Ω_{n+1}^{(n+1)} in the multi-domain construction, not on all of T^{(n+1)} | Parenthesis added to Step 1 (CRE (3.10), p.248's "y ∈ Ω₁^{(1)}"; T^{(n+1)} the single-domain reading of RG1) | map l.196 |
| m4 | Step 3's convention has no BCH remainder; Step 6 mentioned one | BCH clause dropped from Step 6; the principal logarithm, not used, differs from the sum by the square of the sum | map l.196 |
| m5 | Thresholds implicit (c₄(d, L), M's domain, a₁; smallness of L²α₀, dLα₁, c_G(C_w + 2d)α₁); the older-layer step should state the rescaling | Step 7 states the thresholds and that they are met on (4)(e)–(f)'s polydisc for g_K small (α₁ ≤ h_k, α₀ = α_{0,k+1} small); the rescaling exp(iη𝐇_k) = exp(iη_j(L^{j−k}𝐇_k)), η_j = L^{−j}, written into the older-layer step | map l.196 |
| m6 | READINGS l.72 said "no new reading" though four mild readings were made; sources list omitted CRE p.267, REG p.78, CMP 98 pp.29, 34; stale labels (Q6) | READINGS l.72 lists the four readings ((2.1)'s 𝐆 is (0.19)'s functional; U_k′(1) = 1; "L−1/2" is (L−1)/2; CRE (3.10)'s V_k(y,x) are (0.11)'s variables) and the pages; the five stale labels updated (l.196 (b) twice: v₁ = 1 at B′ = 0 outright; the size-bound heading without "what is missing"; l.653 "What route (i) would need (not available; route (i) is not used)"; l.643 (C_w + 3dL^{j−k})θ^{k−j−1}h_k for w_tot; l.869 Scope names the case that holds) | READINGS l.72; map l.196, 643, 653, 869 |

Also applied: the n = 0 term in l.194 (d(L−1)η); the status labels at l.176, 194, 196, 216, 654, 869, 982, 1418 now read "reviewed in rounds 40–42, the complex-background step not reviewed".

Not in the packet, noted by the referee as not opened: CRE pp.276–277 (R-bg), CMP 98 pp.30–31, 33, 39, VAR p.307, and (6)(e)'s treatment of u_k at complex backgrounds. Step 8 cites that treatment (*The argument bound at complex 𝐔*, map l.972) for the use of CMP 98 at complex data.

## Not re-reviewed

The six minors above; (d′) Step 8; the round-41 minors; the round-39 F-1–F-4 repairs in RC Pass 6 (f); map l.972 after round 38's n1, n2.

## Sources read for the triage

RG1 p.252 l.39–40, p.253 l.17 and l.36, p.254 l.3–16 (G^c, the means on G^c, (0.12), the extension of [12]'s results); the map l.190, 194–196, 319, 448, 503, 636–643, 653, 869, 972 (excerpts), 982, 1418, 1496; the review in full.

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.176, 194, 196 (Steps 1, 5, 6, 7, new Step 8, (b) twice, the heading, the ũ bullet), 216, 641, 642, 643, 653, 654, 869, 982, 1418 (8e6cd4c4437f → 3fe708bf1a2b, 1614 lines, LF).
- READINGS_RECHECK_2026_10_23.md: l.72 (round-42 status, the four readings, Step 8's sources, the pages).
- WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md: status after round 42; "Open after round 42".
- SESSION_HANDOVER.md: entry appended (hashes there).
- This file (new).
