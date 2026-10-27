# Round 41 Triage (16:34, 26 Oct 2026, date)

Two headless CLI referees (claude-opus-5-5, launcher verification\isolated_reviewer\run_app_review_cli.ps1, packets by build_round41_review_packets_20261026.py with the round-40 reviews as prior reviews), launched 16:07 on the round-40 repairs. Reviews: reviews\it1-d2-base-20261026-r2\review.md (exited 16:25) and reviews\it1-d2-rep-20261026-r2\review.md (exited 16:27). Map at launch cce46318b239; after this triage 4ae76e8f6709 (1614 lines, LF). READINGS 6ce272b2db7a → b5234f189a20; closure dbaa47c63eb4 → 3cc6ecac4c77. V4 563736a8dfb9 (unchanged since 14:41; cited by label).

## Open after this round

- **OPEN, D2.2(4)(d) for k ≥ 2: the representative of the ω-dependent factors.** Unchanged from round 40, now stated in full (round 41 m4): a k-uniform bound on the B′-variation of ρ̄_k(V_k)(Γ^{(k)}), the analyticity of v₁ in complex B′, the older-layer form C_wθ^{k−j−1}h_k, the multi-domain chains, and the gauge of VAR's reference U₀ (p.280 fixes U_k's gauge only). What closes it: D(k)'s frame made explicit by (c)'s output convention; a candidate route recorded from the review, not certified: under (c)'s convention ρ_{k+1}(W) = ρ_k(V^{(k)}(W)) with V^{(k)} in RG1 p.265's G(V) = 0 gauge posed on the mean variables (p.266, (2.5)), so M^n(ρ_k) would satisfy the absolute mean axial condition in every (n+1)-block and the k = 1 holonomy argument would extend level by level (Σ_{n<k}d(L−1)·2L^{n−k} ≤ 2d).
- **Reading R-bg, new (round 41 S-A):** the real-part membership of U_{k+1} on the older layers (and so on the layer n = 1 for k ≥ 2) is Bałaban's statement CRE p.276 l.10–12 with p.277 l.3–8, accepted; its quantitative form (the responses to the data changes on Ω_{j+1}, j ≥ 2, bounded on the layer n = 1 by (190)'s decay against the margin β2^{−k}α_{0,1}L^{−2}) is not written. The reviewer's sketch is in §(A) below.
- **Not re-reviewed:** the round-41 minors (map l.174, 183, 194, 196, 654–655, 921, 922, 970, 975, 976, 981, 982, 1418); the round-39 F-1–F-4 repairs in RC Pass 6 (f); map l.972 after round 38's n1, n2.

## (A) it1-d2-base-20261026-r2: the base points on Ω₁∖Ω₂ at k = 1

Verdict: no fatal finding; one serious (S-A); minors m1–m8. At k = 1 "correct and sufficient for its purpose" once the minors are tidied. Prior findings: F1, S2, M1–M8 closed; S1 partly closed (R-h wording).

| Finding | Content | Disposition |
|---|---|---|
| S-A | The k ≥ 2 status cites R-m, the complex-margin statement for (2.36)–(2.39) (l.183, l.698); "no regularity improvement" (p.277 l.3) is not a preservation statement; U_{k+1} ≠ U₂ on the layer n = 1, and (2.34) constrains ∂U itself. Closest print: p.276 l.11–13 ("Other bounds involve regularity properties of the configuration U_{k+1} on a neighborhood of Ω_n∖Ω_{n+1}, and these are the same as for U_n-configurations"), qualitative. Repair offered: a decay-and-margin derivation (responses to the data changes on Ω_{j+1}, j = 2, …, k, each O(ε_j) at its source (p.267 (3.14)), bounded on layer 1 by (190)'s decay at the a priori regularity, dist(Ω₃, Ω₂ᶜ) ≥ 2MR₂ layer-2 blocks, sum ≤ Cε_Ke^{−cMR₂}, absorbed by the margin since e^{−cMR₂}ε_K/α_{0,1} → 0 with R₂ ≥ (log g₂^{−2})^r), with strict constant conditions; alternative: cite p.276 as a reading. | Accepted. The alternative taken: new reading R-bg (p.276 l.10–12 with p.277 l.3–8; Bałaban's, accepted under the standing rule) entered in the gaps block l.183 and in (6)(e) *The real background* (l.921), and cited in l.174, 922, 970, 976, 981, 1418 in place of R-m. The quantitative derivation is not written; the sketch above is the route if it is wanted. The reviewer's "g_K/g₁ ≤ g₁^{−1}" in the sketch is not checked here. |
| m1 | "by R-h … acts on no component for k ≤ N" overstates R-h (basic step only; l.326: the rest is D2.7's check). | Applied in l.976 and l.174. |
| m2 | Citations: the δ is in (1.11), (1.14)–(1.15), (2.21), not (1.12); the U₂ problem is (2.12) with p.266 (3.10); (2.2)–(2.3) are on p.255. | Applied (checked in the transcriptions: (1.11) carries δ(ŪV^{−1}); (2.12) is the minimal-orbit map on regular V; (3.10) on p.266). |
| m3 | p.267 prints "[16]"; "[15]" is the transcription's correction. | Applied. |
| m4 | VAR (1) not checked; the corner-convention plaquettes beyond Ω₁^∼ are covered by p.248's χ₀ on □ ⊂ Ω₁^∼ (p ⊂ □^∼), not by V4 (B1)(i). | Applied. |
| m5 | "≤ 2R₁^VM₁η" should be strict (alignment ≤ M₁η); "exceeds the sides" needs 2R₁ > √d(C + 8R₁^VM₁/M). | Applied with 9R₁^VM₁/M (the 4R₁^VM₁/(LM) term absorbed). |
| m6 | "any B ≥ 1 works" only under q₀ > p₀; strict ">" for the q₀ = p₀ constant. | Applied in l.976 and l.174. |
| m7 | Withdrawal wording ("grows like", "fails"). | Applied: "the constant certifiable from the characteristic functions", "bounds only by 2(1+β₀)²√k ε₁", "cannot be verified this way". |
| m8 | Labels: l.922, l.970 lacked "repairs not re-reviewed"; "reviewed (round 40)" omitted that it was fatal; l.975's pointer for D₀ named *Derived instead of assumed*. | Applied (labels now "reviewed in rounds 40 and 41, the round-41 minors not re-reviewed"; l.174 names round 40 as fatal; l.975 points to *The base point on Ω₁∖Ω₂* for D₀). |
| context | l.922's "VAR Thm 1 for U_{k+1} with the global ε_{k+1}": at k = 1 the (7)-constant is ε^V = 2(1+β₀)²ε₁ ≤ 2(1+β₀)⁴ε₂, not ε₂. | Noted in l.922. |

Also noted by the reviewer: sec:c3-9-1 is used as a template at the step 1 → 2 (it treats U₁ at the step 0 → 1), the class-(6) membership coming from R-reg and the identification from Theorem 1's uniqueness; written into l.976.

## (B) it1-d2-rep-20261026-r2: the representative and the frame of σ_j

Verdict: no fatal, no serious finding; minors m1–m7. Prior findings F1, S1, S2, M1–M5 all closed (M5 up to the READINGS marker). The k = 1 bound "correct and loose (d(1 + o(1)) suffices)".

| Finding | Content | Disposition |
|---|---|---|
| m1 | At k = 1 the analyticity of v₁ in complex B′ was not stated and the (1 + o(1)) dropped. Repair: v₁(x) = U₂(Γ_{y,x})^{−1}M({Ad_{u₁(y)}h_Γ(e^{iη𝐇₁}U₂)}_{Γ∈𝐆(y,x)}) exactly (RG1 (0.5)–(0.6)), analytic in 𝐇₁ (M analytic, p.253; u₁ analytic for |𝐇₁| < a₁, p.266), depending on 𝐇₁ on B(y) only; C_w + d(1 + o(1)) ≤ C_w + 2d. | Applied in l.194, 196, 654–655 (constant 2d throughout). |
| m2 | The discrepancy cost misses ‖Ad_{w(b₋)}‖ ≤ e^{2c_G|log w|} for G^c-valued w; with 𝐇^{(j)} in the frame before rotation and the cumulative Σ, the final 4S_H/g_j, 10S_H/g_j and 40 stand. | Applied in l.982. |
| m3 | Σ_m C_wθ^{m−j−1}h_m ≤ C_wh_{j+1}/(1−θ) needs h_m ≤ h_{j+1}, not given by (2.6). Repair: h̄ := h at the coupling (1+β₀)g_K. | Applied. |
| m4 | The OPEN entry names only the size bound; add analyticity in complex B′, the older-layer form, the multi-domain chains, VAR's reference gauge. | Applied in l.194 and l.654–655. |
| m5 | READINGS l.69 still states the withdrawn (B) under "closed". | Applied: withdrawn-marker in the l.69 header. |
| m6 | The provisos: proviso 1 would give v₁ ≡ 1 under (c)'s convention; proviso 2 is exact only for x-based relative variables; neither is the sources' reading (CRE p.247 fixes (0.11)'s mean variables; VAR p.280 cites REG (1.19)). | Applied: the readings stated as the sources', the alternatives as remarks. |
| m7 | θ_b (the cutoff) and θ (the decay ratio) clash in l.982. | Applied: θ_b identified as (6)(a)'s frozen cutoff value g(A_j′(b)) ∈ [0, 1], distinguished from θ. |
| pointer | Route for k ≥ 2 through RG1 p.265's G(V) = 0 mean gauge (above), "a direction only". | Recorded in l.194 and above, not certified. |

Also verified here: RG1 p.252 (𝐆(y,x) the shortest monotone contours, |n_μ| ≤ (L−1)/2, so loops of ≤ d(L−1) bonds); RG1 p.253 (0.5)–(0.11); CRE p.247 ("U(y,x) are the variables introduced by (0.11) [I]").

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.174, 183, 194, 196, 654–655, 921, 922, 970, 975, 976, 981, 982, 1418 (cce46318b239 → 4ae76e8f6709).
- READINGS_RECHECK_2026_10_23.md: l.69 marker; round-41 bullet.
- WILSON_IT1_D2_OPEN_ITEMS_CLOSURE_2026_10_26.md: status after round 41.
- SESSION_HANDOVER.md: entry appended.
- verification\isolated_reviewer\build_round41_review_packets_20261026.py and the two cli_brief.md (new).
- This file (new).
