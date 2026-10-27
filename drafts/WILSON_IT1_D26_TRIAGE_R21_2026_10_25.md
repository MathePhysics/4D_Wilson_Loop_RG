# Round-21 triage of the D2.6 closure (25 Oct 2026, from 01:39, date)

Reports: verification/isolated_reviewer/reviews/it1-d26-s{2,4,5,6,7,9}-20261025-r2/review.txt (claude-opus-5-5, landed 01:09–01:15), all read in full. No fatal item in any packet. Every serious item is repaired in WILSON_IT1_D26_CLOSURE_2026_10_24.md as listed below, or kept OPEN with the reason.

Sources read for the repairs (01:20–01:39): CRE pp.256, 257, 266–272 (transcriptions); V3 L470–480 (Lemma charts), L600–610, L2446–2452 (§c5-3-4(a)), L2594–2602, L2730–2751 (Lemma c5-5-7z and proof), L2785–2808 (Lemma c5-5-8 and proof), L4617–4623 ((c4-6-5)), L4876–4892 (§c4-10-1); ONE_LOOP_PROOFS.md l.80–111 ((W), Lemma 2.1) and l.716–743 (Thm 8.1, Cor. 8.2); RG1 p.257 (linear size); LFR II p.380 l.28 (d′ in MR_j-cubes), p.384 l.19–36; map l.279, l.292, l.303–304, l.1529–1530, l.1599–1601, (14)(c) l.1625; IT-1 note l.1757, l.1760.

## s2 (§§0–3)

- **S-1 (2.1(a) extent and premise).** Repaired. 2.1(a) now uses (14)(a)'s interval extent ext_{k+1}; premise R_t − C_boxM < M(ext_{k+1}+1) for t ≥ 2 by minimality of t, R_2 = 3C_boxM for t = 1; d^Z_{k+1}(n) ≤ 2M·ext_{k+1} + (3C_box+2)M. The distance is paid by e^{(ν_e/4)ext_{k+1}} at rate c_* := ν_e/8. The carried weight is e^{(3/8)ν_e·ext^{coll}} from the remaining e^{(3/4)ν_e·ext_{k+1}}, since ext^{coll} ≤ 2ext_{k+1} + 3C_box + 1 (s5 S-B's split).
- **S-2 (coll sizes).** (a) Repaired: (14)(d)–(f) are re-run at amplitude b_k with the per-slot bounds of 2.2 *Size*, constant C_S″, KP condition a smallness of g_K. (b) The description is corrected: ω′ enters (3.27) through the source term, 𝐏^{(k)}(g_k,(A_k,A)), the 𝐄_k-terms at U_k(…) and V^{(k)}(S_{k+1},(A_k,A)). CRE pp.271–272 print the expectations under (3.29) at tA_k, t ∈ [0,1], and file the resulting terms as boundary terms of 𝐁^{(k+1)} ("contributes to 𝐁^{(k+1)} only"). The use of (10)'s bounds at fixed A_k ≠ 0 is logged as reading R-src (Bałaban's practice on pp.271–272), replacing the unlabelled "input".
- **S-3 (§3 status).** Repaired as bookkeeping: register R6 now reads "§3; not closed: rests on O1 and O3 (OPEN) and R-m (reading)". The k ≥ 2 VAR-Thm-1 route is not taken; R-m stays the reading used.
- m1 (G2) swapped back to the print (2MR_j for the RG domains Ω_j, Λ_j; L^nξM₁ for 𝐁_j(Ω)). m2 §3 tail parenthetical corrected (w_t = (t+1)³e^{−η_wt}). m3 wrap(k+1) kept in (ii) as the map does, with the bound Cρ̂_{k+1}e^{−(ν_e/8)N^{(k+1)}_min} from ext_{k+1} ≥ N^{(k+1)}_min/2 − 1, summed under (5)(g)'s torus condition; not carried by §5. m4 precedence: 2.1's tests are applied to the final merged group, att(k+1, coll) first. m5 single species test "meets Coll_{k+1}" in 2.1(d) and 2.4. m6 2.4's extent taken from sh(M) and the clusters' spares, factor 2 removed. m7 transfer restated in #cubes form; d′ = 0 case from RG1 p.257 with LFR II p.380 l.28. m8 rates fixed: c := min(c^{(1)}, ν_e/8, c′); the c_*′ amendment also amends N_j and A_j(Z). m9 wording. m10 2.3: extension marked, R-𝐁 additions completed (exhaustiveness; n < k derived), 2r_k condition restated as r_k < C₁^{CRE}p₁(g_k) with the clash removed, label inherits 2.2's inputs. m11 2.5 label. m12 header sources, *Units*, "available bound".

## s4 (§4)

- **S-A (4.3 distance).** Repaired: the O(ρ_{k+1}) kind-(γ) groups contain a collar cube (their polymer meets Ω_kᶜ ⊆ Λ_{k+1}ᶜ), so they are bounded in 2.2's collar form and are att(k+1, coll) (rule change (3), logged). The interval extent removes the arc-hull question.
- **S-B ((11)(f) at the (α) radius).** Repaired as a scope statement: R-dec's scope is stated to include D2.1(4)'s polydisc |s(Δ)| ≤ e^{κ_s}, |t_YB′|_Y ≤ ε_H, and ε_H is shrunk by R-dec's O(1) (c_πc_CM·O(1)·4B₀e^{16κ_s}ε_H ≤ 1). Logged for the user's review.
- m-a renamed r_k → r′_k with O(1)ϑ ≤ ½ (RM₁ ≥ 32log(4L·O(1))/δ₀). m-b η in the per-bond factor; the per-cube e into e^{−(κ_s−3)#(Y)}. m-c (ii) reworded with SW (b3)'s condition O(1)Lθ ≤ (1−β)/min(β,1). m-d "∂_t" removed. m-e, m-f, m-g, m-h (χ even), m-i moot, m-j moot (collar form), m-k 2.3's argument extended to 𝐄/𝐑-terms with Y ⊄ Λ_{k+1}, m-l labels, m-m partition named.

## s5 (§5)

- **S-A ((T0)).** Repaired: (14)(d)–(e) re-run with the vertex set of new constituents and dev old members; att old members are fixed data; (β)-vertices carry their touched att member's Cauchy factor. The carry is stated in product form through the first-member injection, Σ ≤ Π_D(1 + w(D)(1+m_D)), which is the form §7.2 uses (Π(1+‖Y‖)).
- **S-B (weights).** Repaired: carried rate (3/8)ν_e in ext^{coll} (5.0); (T3) with a = (3/8)ν_e gives c_ne^{−(15/16)ν_eR_{n+1}}; S_R redefined at rate (15/16)ν_e; fixed att vertices carry no interval-extent shares.
- **S-C (bridges through non-component cubes).** Repaired: the descendants are att species, which need no (ii-w) extent weight, so the shares ν_e·41(diam_v+1)/M of map (14)(c) are free and pay e^{−ν_e} per cube along the tree path; cubes of M∖D′ from e^{−(r/648)#(M∖D′)}, vacuum links from e^{#(𝒞)/4}.
- Minors: split before (11)(d) and e^{16ν_e} recorded; pairwise Cor. 8.2 (ONE_LOOP_PROOFS (W) on every window, Lemma 2.1 step 4); 5.5 with F(W) and first-species rooting; D(j+1)(ii′); att-on-𝒟^{sub} "for review"; labels; LFR citation; wrap(j) reconciled (kept in (ii)); lw weights fixed in §6.4.

## s6 (§6)

- **S-A (exposed links).** Repaired from V3: §6 works on the covered event A^fin_cov (V3 L2594), where no contour link has an exterior input (proof of Lemma c5-5-7z(a), L2751). T_i := U₁(r_i) (the map's definition, l.279), T̂_i := U_ξ(m̂)(r_i), so Y_i = π(e^{iΦ_i}) − 1 and the "+1" term is gone. The uncovered event is V3's mark term (L2449) and IT-1 note D1.1 (§3d), not lw's.
- **S-B (complex domain).** Repaired: Y_i = π(e^{iΦ_i}) − 1 has no background factor, so ‖π(T_i)^{−1}‖ never enters; Φ_i is jointly analytic in the complex background and the phase (V3 §c4-10-1, L4880–4892), and Schwarz's lemma gives the complex-data bound with a constant of L and the group. The chart point at complex data is m̂₀ := m̂(U₁) (IT-1 note l.1757). The dependence set is the (R_t + 2R_c)-neighbourhood of i; the extent weight and σ for lw slots are fixed.
- **S-D (budget).** Done: V3 L2791 gives e^{4νσ}M_Λ(W) ≤ C_pinρ_t with b̄_W ≤ 2M_Λ(W) and e^{θ°} ≤ e^{νσ/16} (L2806). At the map's rates ν_r = ν, ν_e = 2ν/C_box the t-family groups need 1/16 + 2 (§3j(6)) + 3 ((ii-w), since ext ≤ C_box(σ+1)) + 7/8 (tail) > 4: overspent. Amendment: ν_e := ν/(2C_box), η_w := (3/8)η_V; then 1/16 + 2 + 3/2 + 3/8 = 63/16 ≤ 4, and (13)(a) holds since ν_eC_box = ν/2 ≥ η_w. ν_r = ν unchanged. Map l.292, l.1529–1530 amended.
- Minors 1–14 repaired (map clauses, own OPEN item (O2′) for merged contour-anchored activities, labels, R_lw ≤ MR₁ as a g₀-threshold, units, joint merge, κ₁ booking).

## s7 (§7)

- **S-A (reserved share).** Repaired: the induction is run for κ̂_j(Z) := κ_j(Z) − Res(Z) − Pol(Z), additive over creation pieces and constant along S; Res is used once, as the component's KP weight in one joint expansion against the link masses summed over the lifetime; small domains get their share from 7.3's ¾p₀(g_j).
- Minors 1–12 repaired (R_n ≤ LR_j; S^m reason; 100^d; (1.84)–(1.85); 2(14)^d; single ε_A payment; K ≥ 8B; τ̂ leftovers and D2.3(9) note; mass form; C_in ∝ M^{d+1} with 7.1's count; dependency notes; τ̂̄).

## s9 (§9)

- **S1 (route (a)).** Repaired: route (a) rewritten around CRE p.257 (2.14)–(2.15) and p.269 with (3.22) (Bałaban's mixed-set practice), the scope question posed as a reading for review, the remaining step named (the interior Γ_i term of size O(δ_i) against (3.7)'s and (3.9)'s requirements), CMP98/VAR pins dropped. O1 stays OPEN.
- m1 OPEN set = □′^{∼4} ⊄ Ω_{i+1}; inner-band □′ with □′^{∼4} ⊂ Ω_{i+1} moved to the derived bullet. m2 χ_Ax derived. m3 (3.10). m4 roles in §9.2. m5 R-avg on p.267. m6 R-ζ named, ζ/R-h sentence moved. m7 (3.19)'s domain. m8 boundary-layer input on Γ_{i+1}-blocks marked as resting on [14] (1.65) (not read). m9 □′^{∼2}, "not derived". m10 reading label. m11 VAR sizes dropped. m12 §9.2 attribution. m13 (G2), "only through", OPEN status from §8. m14 (T-dev)'s consumers listed.

## OPEN after round 21

- (O1) R14's cubes □′ ⊂ Ω_{i+1}^∼ with □′^{∼4} ⊄ Ω_{i+1} (§9.3).
- (O2) the extra-label step (D2.2(3)(b)), and (O2′) acceptance of merged contour-anchored activities in the label sum (§6.5), split by s6 minor 2.
- (O3) the k = 1 base points on Ω₁∖Ω₂ (D2.2(6)(e), not D2.6's; used by §3, §5.1, §6.4).
