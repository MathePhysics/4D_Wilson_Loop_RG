# Triage: LF part 13a2, round 5 (lf-p13a2-20261107-r5), 7 Nov 2026

## Verdict

Not clean: three minor findings (m1–m3) and four trivial ones (t1–t4). No fatal or serious finding. The clean count of 13a2 stays 0.

LF reviewed at 22a21c559148; repaired together with the 13b r2 repairs, LF b94d3e5f0d86. Table 900516237706, LABELS c8d0a06d99da; the table rows these repairs restate were sent to the fork (21:58).

## Repairs

| Finding | Where | Repair |
|---|---|---|
| m1: Lemma 2.1(i) bounds g_k^{−2} with the unit coupling g, not ḡ | #4.55-0.1; #4.41-1-1 (packet 11b); table #T3.33 | Both runs are pinned at the unit coupling ḡ (Cauchy #C1.1-2: g^A_K = g^B_{K+1} = ḡ), so Lemma 2.1's g is ḡ, and the ḡ-form holds as written; #4.55-0.1 now cites this. The same pin makes #3.30 and #3.39-1 correct. In #4.41-1-1, g_{j(x)} ≤ (1 + β₀)ḡ by CRE (2.6) and (1 + β₀)² ≤ 2 give (1 + 2b₂ḡ²)g_{j(x)}^{−2} and C_∇ := (1 + c_ζ)(1 + 2b₂ḡ²) + 4c_{2.24}b₂ḡ²; C_pr in #4.54-0.1 takes (1 + 2b₂ḡ²). #T3.33's "CRE's bound on g_k" is to be corrected by the fork |
| m2: D″^B carried no coupling label | #4.54 | Both data use run A's coupling in exp(ig_kB), which conjugates their ratio by a unitary; the comparison of the two runs' couplings is §4(d), *The couplings.* |
| m3: the regularity of the data plaquettes meeting V″ | #4.54-0; #4.43-1.2 and #4.50-1.1.0-1 (13a1) | D″^A satisfies VAR (7) on all of 𝐁″_k with §1's ε₁, the mixed plaquettes at the layer boundaries and at Λ ∩ Ω″^{∼2}_{h+1} included (#1.3, #1.7), and this is ≤ (1 + β₀)(1 + A₁/A₀)Cε_k ≤ ε₁: ε_j + ϑ_j = (1 + A₁/A₀)g_jp₀(g_j) (#1.6), g_j ≤ (1 + β₀)g_k, g ↦ gp₀(g) increases on (0, e^{−p₀}), which contains (1 + β₀)g_k by #4.50-1.1.0-1. C(M) ≥ (1 + β₀)(1 + A₁/A₀)C is added to #4.43-1.2. #4.50-1.1.0-1 now carries (1 + β₀)²γ < e^{−p₀} in place of the unused 4Lδ′_k ≤ ε_k |
| t1: "only the derivative bound below uses it" | #4.51-1.1 | Clause deleted |
| t2: sup_Λ abs(A) | #4.53-1, #4.53-1.1 | The sup runs over the averaging blocks of the data of Λ, which lie within one block of Λ, so in the layer k of 𝐁_k(Z) (#4.44-0.2); #4.53-1.1 reads "on these blocks" and "on every block of the layer k" |
| t3: adjacent layers of 𝐁″_k | #4.54-0.1.2 | #4.48.0 holds at the blocks of 𝐁″_k, whose layers below the top are ≥ LM₁ wide, so only adjacent layers meet (BP_LAYER_WIDTHS #4.18-1, #4.18-2-2) |
| t4: the run of U_t | #4.54-0.0 | "is run A's VAR minimiser" |

## Consumers outside 13a2

- 11b (done): #4.41-1-1 changes a constant only (the factor 2b₂ḡ², 4c_{2.24}), with the derivation in the line. This is a content change in a done packet, so 11b's next content round sees it. The bound's form is unchanged.
- 13a1: #4.43-1.2 (one more lower bound on C(M)) and #4.50-1.1.0-1 (the smallness of (1 + β₀)²γ). The r6 build at LF 22a21c559148 is stale and is rebuilt.
- Table: #T3.33, #T12.9 (C_∇, C_pr), sent to the fork.

## Pre-check, lf-p13a2-20261107-r6

- Changed lines re-read after the fork's relabel, at LF 400c5fa76246: #4.51-1.1, #4.53-1, #4.53-1.1, #4.54, #4.54-0, #4.54-0.0, #4.54-0.1, #4.54-0.1.2, #4.55-0.1; in 13a1 #4.43-1.2 and #4.50-1.1.0-1; in 11b #4.41-1-1.
- Cited displays re-read: Cauchy #C1.1-2; CRE (2.6) (p.255 l.42–50); LF #1.3, #1.6, #1.7; BP_LAYER_WIDTHS #4.18-1, #4.18-2-2; BETA Lemma 2.1(i); table #T3.33 as the fork entered it (the pin and g_k ≤ (1 + β₀)ḡ).
- Derivations checked: (1 + β₀)² ≤ 2 gives g_{j(x)}^{−2} ≤ … (1 + 2b₂ḡ²) in #4.41-1-1 and C_pr; at the layers j ≤ k, ε_j + ϑ_j = (1 + A₁/A₀)g_jp₀(g_j) ≤ (1 + A₁/A₀)(1 + β₀)g_kp₀((1 + β₀)g_k), and p₀((1 + β₀)g_k) ≤ p₀(g_k) since p₀ decreases in g, so §1's ε₁ ≤ (1 + β₀)(1 + A₁/A₀)Cε_k ≤ ε₁. The last step was implicit in #4.54-0; it is now stated there, citing #T10.2, and the line (852 characters) is split in place: #4.54-0 holds D″^A's regularity and the new #4.54-0-1 holds the data path, with the D-tags #D.D″_t and #D.ε_D″ (LF ff32ad403ddb, relabel requested from the fork).
- Grepped: ḡ in the LF and the Cauchy note (#CP.13–#CP.14 consistent with the pin); C_∇ and C_pr (LF and table #T12.9); "C(M) ≥"; 4Lδ′_k (no remaining use).
- No forward tag citations in the changed lines.
- Part size: 11,751 characters of reviewed blocks at r6 (10,841 at r5, ≤ 25k); the growth is m3's derivation of D″^A's regularity, its p₀ step, and m2's coupling sentence.
- Spec spec_p13a2_r6.json: prior = the r5 review; permitted background adds BP_LAYER_WIDTHS #4.18-1, #4.18-2-2, Cauchy #C1.1-2 and table #T3.33; questions 3 and 4 name the regularity of D″^A and the pinned coupling; the stale 𝔯, ε₂ and ε₃ entries were updated.
- Built: reviews\lf-p13a2-20261107-r6 at LF ff32ad403ddb, table d3fd1c0fcdf7, LABELS 3371dd395591, with 0 definition conflicts (7 allowed); a build at 400c5fa76246, before the p₀ step, was never launched and was removed.
- Launched after 13a1 was done (r7 clean, full). The LF changes since ff32ad403ddb lie in 13a2's background: 13a1's #4.44-0.2, #4.46, #4.46-1, #4.46-1.1, #4.48-3.0.3, #4.48.0, #4.48.0-2, #4.48.0-2.1, #4.50-1, and the 13b re-point #4.561.1-2. There is also the bookkeeping move of {#D.Δ} from #4.44-2 into #4.51, so the snapshot stands. The next 13a2 round sees these.
