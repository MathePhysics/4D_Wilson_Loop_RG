# Background-Iteration Closure, Round r5 (it1-bg-20261109-r5): Triage

Packet: reviews\it1-bg-20261109-r5, a full round on note 96f8f4c2ab91. Its pre-check is in WILSON_IT1_LF_TRIAGE_BG_R4_2026_11_09.md, *Pre-check for r5*.

## Verdict (report read in full, 13:0x, 9 Nov 2026)

Not clean. There is no fatal finding, one serious finding and six minor ones. The referee found every inequality of §3.2 (l.70–84) correct, and also its consumers l.153–156 and l.166–169.

## Repairs

Line numbers are the snapshot's.
- **S1** (l.114, l.168, header l.3–6): (iii-d) stated only 15.4(ii)'s three bounds. But the coarse chain's D(K) form at K > N (l.16, §3.1, l.81) needs all of D2.7 item 15.
  - User instruction (13:0x): "Close the gap!".
  - Repair: (iii-d) is now D2.7 item 15 (15.0–15.8-1) for the coarse chain's 𝐑-steps. It is derived in §4.3, given (iii-a)–(iii-c) (with the coarse clauses on the domains of TL #48) and (iv-a)–(iv-c), under a new condition (C4R).
  - The derivation runs as follows:
    - Item 15 uses the words and insertions only through covariance, the dependence set, the sup bounds, analyticity on LFR II (1.65)'s value space and at TL #7's points, translation covariance, and D(j)'s register. 15.8-1 was read in full for this.
    - The coarse words have these properties: 4.1(1)–(2), the scale-k lattice inside the MR_j partition, and M^k commuting with scale-k translations.
    - On both evaluation domains, the per-plaquette bound is at most 3.1(1+β₀)α_{0,K} and the per-bond phase at most 3.1(1+β₀)α_{1,K}. These come from LFR I p.190 (i), (1.66), (1.68) with L₀² ≤ L/3 (p.191), and from CRE (2.34), (2.39) with #T4.47 and #T4.49's coefficients.
    - Hence 4.1(3)'s chart conditions hold at fixed k, and τ_c ≤ 2.
    - a_j changes only in its arc term, 1280c_πc_h(b_d^c)^kα_{1,j}MR_j in place of 1200c_πα_{1,j}MR_j, and in C_α by (1.01)^d. So ĉ₁ ≤ e^{−p₀/2} still holds, with a threshold that depends on k.
  - So 15.4(ii) holds for the coarse gas with table #T4.37's C^R_E and c^R_E. r^{R,g}_K, r^{R∨}_K and C^{R∨}_E are deleted, and r^R_K and C^R_E serve both chains.
  - Consumers updated: the header, l.78, 80, 81, 82, (C5), (C6), the constants list and the closing lists.
- **m1** (l.115): "What it needs" omitted translation covariance, (D1) and (D3). It is replaced by the derivation, whose first sub-line lists every use, translation covariance included.
- **m2** (l.188–189): the closing lists now name (iii-d). The list of Bałaban statements now reads CRE (2.4)–(2.7), adding LFR I p.190–191 and CRE (2.34)–(2.39).
- **m3** (l.78, l.169): r^{R,g}_K is deleted, because the coarse chain has r^R_K itself (S1).
- **m4** (l.82): the line now cites (iii-d) for the coarse half, with C^R_E.
- **m5** (l.75): CRE's indices are now written "with its indices n, m set to K, j". The letter m is then only m := K − j.
- **m6** (l.70): j = 1 is now attributed to #MD2.0.3.52-1 (its sum Σ_{j≤k} includes j = 1), and #MD2.3.7.3 is cited only for n_j.

## Bookkeeping in the same pass

- After (4)'s consolidation (map 490f2a5102c2), every map tag in the note and the table was checked against the live map.
  - Two table pointers were deleted: #MOMGD.1-2 and #MOMGD.5-14, both in #T12.13.
  - Their definitions stand at #MD2.4.11.5-18 (C_{c₀}) and #MD2.4.12.51-3 (C_S′), which the row already cites, so the dead tags are removed.
- Map ec5925fddaa0 (a further consolidation) deleted #MD2.3.4.26-1, #MD2.3.4.29-2 and #MD2.4.3.12-5. These were the only dead tags among the 429 map tags of the note and the table.
  - #T12.13 drops #MD2.4.3.12-5; its A_h, ϖ and η keep #MOMGD.14-3, #MOMGD.14-5 and #MD2.4.3.12-2.
  - #T12.16's per(P) and s(Δ̃) are deleted, since no file defines or uses them now.
  - Relabel gives LABELS 995dc14c3fec and table 0a450e93e7fc, and defcheck prints 0 lines.

## Pre-check for r6 (13:4x, 9 Nov 2026)

r6 is a full round of the repaired part, on note 44f58683dac5.
- *Changed lines re-read in full:* the header l.3–6 and l.12; §3.2 l.70–84; (iii-d) l.114–147; (C4R)–constants l.198–202; the closing lists l.215–217, l.222–224 and l.228–240.
- *Repairs in this pass, after a re-derivation of (iii-d):*
  - l.124 now says k ≤ j (4.1) for the bound 2L^{k−j} ≤ 2.
  - l.138's cube count is now derived: (100R_j + 2)^d ≤ (101R_j)^d, from the projection length 100MR_j + 4 < (100R_j + 1)M. No alignment of the cube with the M-grid is assumed.
  - l.139 now says c_hφ_c ≤ θ^R ≤ 1/10 follows from (C4R).
- *Symbols:*
  - t^R, θ^R, τ_c, θ_c, φ_c and D^R_c occur in no other file: not the table, the LF, balaban_proofs/ or D2.7.
  - (C4R) is new, and every use of it in the note is consistent.
  - r^{R,g}_K, r^{R∨}_K, C^{R∨}_E, C^{R,g}_E and c^{R,g}_E occur nowhere in the note.
- *Quotations checked against the source:*
  - D2.7 15.5(i): the arc factors 2e^{1200c_πα_{1,k}MR_k} and e^{3c_πα_{1,k}abs(C∩X⁺)}, and abs(C∩X⁺) ≤ 400MR_k.
  - D2.7 15.5(ii): the word on (1.65)'s space with τ_i := e^{3c_πα_{1,k}} ≤ 2, and #cubes(Y₁), which is 1 for a bond meeting no component and ≤ (100R_k)^d for the arc word.
  - D2.7 15.5(β): C_α := 2O(1)e^{(κ₁−1)/4}(100R_k)^d, and a_k(X) with its term 1200c_πα_{1,k}MR_k.
  - D2.7 15.5(α′)(3): the s-points lie in 𝒟^{♮,3}_k, and the members are analytic and bounded on 𝒟^{λ,3}_k. #7 is cited for the evaluation points.
  - D2.7's bullet *Item 15's amplitudes*: ĉ₁ = e^{3+a_k}e^{−p₀(g_k)} ≤ e^{−p₀(g_k)/2} needs p₀(g_k)/2 ≥ 3 + a_k.
  - CRE p.261, (2.34): abs(∂U − 1), abs(∂𝐔 − 1) < f α_{0,n}ξ²(L^nξ)^{−2}. (2.39): L^nξabs(A′) < f α_{1,n}, with f = 1 − β(1 − 2^{−(j−n)}) ≤ 1.
  - Table #T4.47: f♮_n = f_n(1 + ¼β2^{−(k+1−n)}) ≤ 1 + β/8. Table #T4.49: 𝒟^{♮,3}_k's coefficient on Ω_k is 3f♮_k = 3(1 + β/8), with (2.38)–(2.39) kept. #T3.39: β = 1/8. Hence 3f♮ ≤ 3.047 ≤ 3.1.
  - LFR I pp.190–191 and LFR II p.375 l.29–35, as recorded in r5's repair S1.
  - The monotonicity: x(log x^{−2})^q increases exactly when x < e^{−q}, so α_{i,n} ≤ (1+β₀)α_{i,K} under (C2′) with q₀ = q₁.
  - e^x − 1 ≤ 1.06x for x ≤ 1/10, since e^{0.1} − 1 = 0.10517.
  - 3·1.06 = 3.18 ≤ 3.2, and 3.2·400 = 1280.
- *Size:* the reviewed blocks total 19,473 characters, under 25k. (iii-d) grew by three clauses, each a derivation step, not a restatement.
- *Snapshot SHAs:* note 44f58683dac5, D2.7 55d8246f93a0, map ec5925fddaa0, Cauchy 785c3a36fed5, table 0a450e93e7fc, LABELS_LF_AND_TABLE 995dc14c3fec, LABELS_D2_STEP_MAP 96d3fc63f8a1, TL note 4c2d342a9417, LABELS_TWO_LOOPS d78ca7718b9d, BP_TL_EVAL_POINTS 18bb0d681b30.
- *Queued for after r6 (13:5x, from two-loops):* two-loops points out that TL #222-2 gives Φ(𝐔) ∈ 𝒟^{λ,3}_k only for 𝐔 ∈ 𝒟^{ev}_k (#222-1, #222.1). 𝒟^{ev}_k is the set of points where the next T-step evaluates, with data in 𝒟^λ_{k+1} (#54). So l.142's "the coarse members are evaluated at the same points" needs the coarse T-step's points to lie in 𝒟^{ev}_k.
  - Re-derived: the step map's operations do not depend on the observable (§1.1, l.22). The composed slots are evaluated at D2.1(4)'s deformed background 𝐔 = e^{iη(𝐇_j(s,B′_j)+a′)}U_{j+1} (§4.1, l.98), the fine chain's. The 𝔖_k slots are insertions in the integrand and change neither 𝐇 nor the data. Hence the coarse chain's next T-step evaluates at points of the same 𝒟^{ev}_k.
  - Repair, after r6: state this inclusion in l.142 in place of "These are statements about points".
- *Known weak points:* none in the lines under review. (iii-d) is conditional, by statement, on (iii-a)–(iii-c) delivering the coarse clauses on 𝒟^λ_j; this is stated in the header, in (iii-d) and in the closing list.
