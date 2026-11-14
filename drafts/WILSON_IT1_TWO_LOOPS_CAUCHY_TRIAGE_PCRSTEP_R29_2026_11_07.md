# Pair Note Triage: pc-rstep-20261106-r29, pc-links_a-20261106-r1, and pc-links_b-20261106-r1 (Pre-Checks)

Two-loops session, 7 November 2026. r28's findings and their repairs are in WILSON_IT1_TWO_LOOPS_CAUCHY_TRIAGE_PC28_2026_11_06.md.

## Found in the pre-read (no round)

- #PC4.14.4-4.5.4-1 named "the att and lw species" among the slot masses, but the young pairs have no lw (#PC4.14.4-4.5.1-1, LF #5.12). It now reads "the att species".
- #PC.1-1.2 pinned LF §5(d)–(e) to the old LF SHA 6e1ff0377576. The pin is dropped, because the packet supplies the LF snapshot and the build asserts its SHA. LF #5.29, #5.44 and #5.50 still say what #PC.1-1.2 takes from them: §5(e) reduces to the points (3), (6), (7) and (10) of (LF-A), derived, not reviewed.
- LF #5.39-3-1-2 (LF-owned) still gives the q = 0 clusters' weighted mass as Σ_c e^{c_off#(X_c∖∪Y_j)}|d_c|e^{|d_c|}, paid by Bałaban's leftover decay. That is r28's refuted F1 argument, and TL #815.2 cites the line. Table #T4.43's C_Ψ″ also lacks "and the weights of #815.2". Both were sent to the LF session (below). r29 waits for the LF repair.
- TL #253, #271, #281, #285 and #288 changed with the links cascade (u_𝔏, L₀^×), and no packet has reviewed them since. They are added to pc-links-a's extracts.
- PC #PC4.8-1.3 (the scales i − 1 < j₀ − 1) and #PC4.14.4-4.5.5 to #PC4.14.4-4.5.5-1 (renamed C_ϑ, #844-7) lie outside these three packets. The C_ϑ and â_* changes in #PC4.6-2, #PC4.9-2, #PC4.12, #PC4.14-1b.8.2 and #PC5.3 are renames (bookkeeping). #PC4.8-1.3 goes to the packet that holds §4.8.

## Peer messages

- To LF (02:50): rewrite LF #5.39-3-1-2 as "weighted size Σ_c y_c ≤ m^w_Ψ per Y_i, y_c = w^Ψ_c|e^{−d_c} − 1| of D2.7 15.8-1(4-1), paid inside two-loops #814's sum by 15.8-1(6) and (6-3) (#815.1 to #815.2), m^w_Ψ := 2C_Ψ″e^{2C_Ψ″}", dropping the c_off clause and the leftover-decay sentence (c_off weights only the pieces other than the D̂_g and the clusters, 15.8-1(4-1)), and make #T4.43's C_Ψ″ "with its joins and the weights of two-loops #815.2, times e³" (TL #814, 15.8-1(6-3)). No bound moves.
- From LF (03:0x): accepted after re-derivation. #5.39-3-1-2 now reads "have weighted size Σ_cy_c ≤ m^w_Ψ per Y_i, with y_c = w^Ψ_c|e^{−d_c} − 1| of D2.7 15.8-1(4-1) …, paid inside the two-loops note's #814 Kotecký–Preiss sum by 15.8-1(6) and (6-3)". The LF also announced two table edits: #T4.43's C_Ψ″ as asked, and #T4.42's c_off clause narrowed to the pieces other than the D̂_g and the clusters, the same misreading. The LF also changed in packet 13 (#4.560-1.1, #4.560-1.1.1). New LF and table SHAs to follow; on arrival, grep TL and PC for the changed tags, re-pin all three specs, and rebuild.

- From LF (during r29): LF e8dfdbf8292b (labels 4841f79dbe0f) changes #4.46 (C₁′ := 4c_tot(1/128)C₁), #4.46-1 (B₅ = 6B₁B₃C₁′), #4.50-1, and #4.560-1.1's p.374 clause. TL and PC cite none of these tags, no C₁′, and no LF definition of B₅. TL's B₅ is Bałaban's own regularity constant, used through (1.84) and (1.87) and #42's C_rsp, not the LF's VAR constant. r29 runs on its 3d177daec646 snapshot. links-a and links-b get re-pinned at their launches. Next, LF ed5712d0a7c9 (labels 75c88aee2b0c) reworded #4.46-2's p.422 factor and split it into the new #4.46-2.1; no bound changed, and neither note cites #4.46-2. Then LF 393a0ba0510f (labels 2fe7a2ccb3db) changed #4.52's quotation of (1.50); no bound changed, and neither note cites #4.52. Then LF 4ad0e9992e08 (labels 9365b8c83175) re-derived #4.46's H₁Y bound from (3.133); no bound changed, and #4.46 is not cited. The LF is frozen during lf-p13 r1, so links-a and links-b pin 4ad0e9992e08.
- From LF (04:4x): p13 r1's minors and m-c are repaired; LF 962274040a17 (labels 6643909545b6), table 8e227609f36c. #T4.43 no longer says "times e³", and LF #5.49-1 cites #T4.43. The other changes are in LF §4(c)–(d) (#4.48.1 to #4.567, #4.197 to #4.200, where c_pl := 2 + 3B₅/C₀ replaces 52). A tag diff against 4ad0e9992e08 confirms that TL and PC cite none of them. The D2.7 15.8 wording waits until links_b r1 finishes.
- To LF (04:11): the links_a launch and its pins; D2.7 69e9e760040e's (6-0) is re-derived and correct; PC -4.5.4-3-2's citation follows the (1-1-1) split; m-c (#T4.43, LF #5.49-1) is needed before r30.
- To LF (11:16): pc-rinputs r1's ρ2 on #T4.44 (R_e = 1 for L > 11; h_box needs only C_box ≥ A_E, #MD2.4.12.7-1), with the re-derivation. From LF (11:2x): accepted. The row will be edited after lf-p13b r2 reports, reading "R_e = 1 for L > 11 (map #MOMGD.14-3, #MOMGD.14-4), so for every L ≥ L₀^× (#T4.42)", with the h_box clause added and the last column "independent of L > 11". Checked: #T4.42 defines L₀^× := 4·10⁴u (two-loops #288), and #288 reads right with this wording. pc-rinputs r2 pins table c94afde7eca1, and the edit changes background only.
- To LF (11:40): n2's #T4.43 wording (D2.7 15.3–15.4, range #814-2–#814-4-2). From LF (11:4x): noted. The #T4.43 and #T4.44 edits come after 13a is done, the table staying c94afde7eca1 until then. LF 105d808e9cb5 (labels 33a41b23ead3) has 13a r2's repairs in #4.43 to #4.55, which TL and PC do not cite (grep, 0 hits). It is pinned in pc-rinputs r3.
- From LF (later): LF 0e208b23ef34 (labels d60a4e6fd2fb) changes #4.43-1, #4.55-0.1, #4.48-3–#4.48-4 and #4.50-1.1, with the new #4.48-3.0.1 and #4.48-3.0.2; the table stays c94afde7eca1. Hashes verified. TL and PC cite none of #4.43, #4.48, #4.50 or #4.55 (grep, 0 hits). r3 runs on its 105d808e9cb5 snapshot, and the next build re-pins.
- From LF (12:4x): LF d3c7bb0f430b (labels 7e6166b24c24) changes only #4.48-3 and #4.48-3.0.1 (the distance step through 𝐁₀, LFR II p.360 l.41–42, LFR I p.195 l.34–35, and p.357's localisation of 1 − ζ₀); the table stays c94afde7eca1. Hash verified at 12:46. TL and PC cite no #4.48 tag (grep, 0 hits). r4 runs on its 0e208b23ef34 snapshot, and the next build re-pins.
- To the table fork (21:4x): #T12.27 at table 67c31cf2ca2d still has bc38 r1's values. It is to be replaced by BC e4152aa6f4ba's: C_{BX} := (24d + 8)√N under √NLt ≤ ρ₀, 4d√NLt ≤ ε, (6d + 2)√NLt ≤ ¼; t(B) and t^X; Θ ≤ e^{d(t(B) + (24√N + 1)t^X)}.
  - δ_F, c₃ and (131) are dropped.
  - New symbols: c^X, ε₁^*, ε₁^X, ε₀^X, r_B, r_B^X. Also BD's ρ₀ (not #T12.8's or #T12.25's), BR's ε and A_d, N of G ⊂ U(N) (not #T12.23's N), and the HS norm.
  - The chain-average source is #BC.1-4-1, and TL #94's constants depend on d, L and G. The SHA is to follow. Until then the bc38 r3 specs mark #T12.27 superseded.

## Pre-check: pc-rstep-20261106-r29 (2026-11-07)

- Changed since r28 (snapshot of r28 against the current notes, in r29's ranges): pair #PC.1-1.2, #PC4.14.4-4.5.1-1, #PC4.14.4-4.5.4, #PC4.14.4-4.5.4-1, #PC4.14.4-4.5.4-3-1, #PC4.14.4-4.5.4-3-2, #PC4.14.4-4.5.4-3-3, #PC4.14.4-4.5.4-4, #PC4.14.4-4.5.4-7, #PC4.14.4-4.13.1; two-loops #814, #815.1, #815.2, #816, #849, #850. Each was re-read. The gate also counts three more lines inside r29's ranges. #PC4.14.4-4.5.1 is re-pointed to #844-4, which names the R-made cross insertions D_g^× and D_G. #PC4.14.4-4.5.5 now reads (1 + C_ϑϑ_k)(1 + ε_k), as in #844-7. In #PC4.14.4-4.5.5-1, G = C_δc̄S_R + (1 + C_ϑ)S^R is at most #844-7's C_δc̄S_R + (1 + C_ϑ + C_attC_y)S^R ≤ log 2. Its Σϑ_k ≤ S^R and Σε_k ≤ S^R are now cited to #774's S^R, not to #844-7.
- F1: y_c = w^Ψ_c|e^{−d_c} − 1| ≤ w^Ψ_c|d_c|e^{|d_c|} ≤ e^{2C_Ψ″}w^Ψ_c|d_c|, so Σ_c y_c ≤ 2C_Ψ″e^{2C_Ψ″} = m^w_Ψ, since #814's sum with the weights is ≤ C_Ψ″ and the dev part (value less flat value) is ≤ 2C_Ψ″ (#815). w^Ψ_c matches 15.8-1(4-1)'s y_c, and 15.8-1(6) and (6-3) pay it (the links by #629-4 from the first eighth, the cubes of the Y_j unweighted).
- m1 to m6 re-checked against r28's review. m1: D2.7 15.4(i) now counts MR_k-cubes, as #816 does. m2: #PC4.14.4-4.5.4-3-3 runs 15.8-1 with C₁ ⊔ C₂, whose 15.8-1(3-1) count (336 = 8 × 42) covers C's eight sides, with the register of #844-3. m3: #803 is the one criterion, cited by #850 and #PC4.14.4-4.5.4-3-2. m4: #PC4.14.4-4.5.1-1 names att(j, Z) and att(j, coll), with no lw. m5: "no '1 +' per piece to exponentiate" in #PC4.14.4-4.5.4-3-1 and #815.1. m6: #PC4.14.4-4.13.1's step is explained.
- Cited lines re-read: D2.7 15.8-1(4), (4-1), (5), (5-1), (6), (6-1), (6-2), (6-3); two-loops #803, #810, #811, #812 to #817, #818, #820, #844-3, #846, #284. 15.8(c)'s cost log 4 + c_W + ν_rσ_k + (3/8)ν_e(R_k(d′+2) + O(1)) has its d′ part paid by κ_k(Y)'s p₀²(g_k)(d′ + 1) and its constant a polylog of order r(d + 1) < p₀.
- Arithmetic: #817 needs 8(d + 1)(1.02)^d ≤ κ; at d = 4 that is 43.3 < 96 < κ. #849's rate is about 2.04ν_r ≤ (5/2)ν_r. #PC4.14.4-4.5.4-9 uses N(Y_i)e^{−p₀/2} ≤ e^{−p₀/4} for small g_k.
- Symbols against the table: C_Ψ″, m^w_Ψ, N(Y_i), E(Y_i) (#T4.43); λ_𝔏, ℓ_P (#T4.42). No restatement of a row. Definition check: 0 conflicts.
- Size: 16,502 characters of reviewed blocks (16,526 before the two repairs).
- SHAs: pair 2852e8eeca59 (labels 080502dd5c82); two-loops 3880cb811b25 (labels b74c687b4bb8); LF 3d177daec646 (labels 80728f9f1fac). Since 8209c13bcd74 only #4.561-1 and #4.561-1.1 changed, neither note cites them, and #5.39-3-1-2 is unchanged. table 9a2e918d956a; D2.7 4070b2971733.
- LF repaired (8209c13bcd74). #5.39-3-1-2 now gives Σ_cy_c ≤ m^w_Ψ, y_c of 15.8-1(4-1), paid inside #814's sum by 15.8-1(6) and (6-3), which is what #815.2 cites it for. #T4.43's C_Ψ″ carries the #815.2 weights, and #T4.42's c_off is narrowed (TL cites #T4.42 only for ℓ_P and λ_𝔏). The other changed LF tags are #4.560-1.1 and #4.560-1.1.1, and earlier #4.560-0, #4.560.1, #4.560-1, the deleted #4.560-1.2 and #4.560-1.3, μ_c, #4.473, #4.499 and #4.540.4. Neither TL nor PC cites any of them. All three specs are re-pinned and rebuilt, with sizes unchanged and 0 conflicts. No known weak point; a clean round is expected.

## Verdict: pc-rstep-20261106-r29

Not clean: 1 serious (S1) and 4 minor (m-a to m-d). r28's F1 (definitional half) and m1 to m6 are resolved. Claims (a) to (d) and (f) are supported. Claim (e) needed the repair below.

How the pre-check missed S1: it checked that 15.8-1(6) names a payer for the clusters' weight, but it did not check each term of D^∪_P (#627) against that term's payer. The per-domain constant 4R_k + 92 is paid by #645 from a first-class component, and a q = 0 part has none.

## Findings and repairs (r29)

- S1 (TL #815.2; D2.7 15.8-1(2-2), (6), (6-3)). The clusters' weight 2^{d+2}D^∪_P carries #627's constant 4R_k + 92 at q = 0 domains, where nothing pays it. Re-derived from #627, #630 to #633, and #645, and from p.389 l.27 to 28, (1.96), (1.97), p.390 l.1 to 4, and p.377 l.14. Repair: TL #812 to #812-1 split F(X′) into its q-parts. At a q = 0 part the constant is 4 (#630, #633). The weight left per q = 0 part is e^{4(2^{d+2}ν_r + (3/4)ν_e)} ≤ e^{0.26} < 2, so the amplitude is 2α^{1/3} = (8α)^{1/3}, Bałaban's (1.97) with 8α, α arbitrarily small for γ small. TL #814 and #815.2 to #815.2-1 are rewritten in place. D2.7 15.8-1(2-2), (2-3), (6), (6-3) were sent to the LF session (owner) with wording. Pending.
- m-a (#PC4.14.4-4.5.4-3-3). It now cites #286's pair condition C_δc̄S_R + (1 + C_ϑ + C_attC_y)S^R ≤ log 2.
- m-b (#812). The q-split is stated (#812), with the reason it leaves the expansion and the bounds unchanged.
- m-c (#814). "times e³" is dropped, since no step uses C_Ψ″ as a lower bound; #T4.43 and LF #5.49-1 were sent to the LF session. The dichotomy at Y_i is no longer needed: #814 roots at the first Y_i a cluster contains, and #812-1 gives that a q = 0 domain contains some Y_i (p.389 l.27 to 28).
- m-d (#816 to #816-1). e^{κ101^d} is scoped to the (6B) and (6C) polymers at Y_i, once per term (#818). The q = 0 parts lie in slotless polymers (c_g = 0 for groups meeting a second-class component, 15.4(i)), summed as Bałaban sums them.
- SHAs after the repairs: TL 865a2afae848 (labels 37c54352753e), PC 5481a1a3fd54 (labels 080502dd5c82). D2.7, the table and the LF wait for the LF session.
- Next: r30, a full round of the same part, after the LF repair. It needs the user's go.

## Pre-check: pc-links_a-20261106-r1 (first round)

- First round, so every line of the packet counts as changed. All of them were read in full: #629 to #629-5, #253 to #258, #271, #281, #285, #288, #491, #520, #538, #570 to #572, #583, #598, #599, #683, #690 to #694, #696, #700, #710, #713 to #714-1, #715 to #721.
- Budget: ν_rλ_𝔏σ + 4ν_eσ ≤ (1/640 + 1/1458)νσ = 0.00225νσ < a°/8 = νσ/256. D2.7 15.8 spends ½, ⅛ and ⅛ and leaves ¼ (its *The links in the gas*). The length-decay eighth: a quarter of it (ν/1024) pays the joins and Ψ, and 3ν/1024 ≥ ν/512 pays the separations.
- Units: (2^d + 8)σ = u_𝔏λ_𝔏σ, and 4 ≤ 24 = u_𝔏λ_𝔏 at d = 4. D2.7 15.8-1(2-5) uses the same u.
- Arithmetic at d = 4 and u_𝔏 = 15360. #254: (21/20)σ + 17 ≤ 18.05σ. #257: arcs 2(32u_𝔏σ + 80); E_{W′} 225σ ≤ 450(½σ + 17); ((8496·17/16 + 11)u_𝔏 + 57600·17/16)/(4·10⁴u_𝔏) = 0.22605 ≤ 0.227 < ¼. #583: (3·17/16 + 9/8)·96 = 414, and 414·64/3 = 8832. #598: 12u(ν_r/8)/L ≤ ν_r/16 iff L ≥ 24u. #696: 8320/(4·10⁴) = 0.208 and 0.208 + 57600/(4·10⁴u_𝔏) ≤ 0.21; the recursion stays below 16.1 + 0.23σ, and 17 + σ/4 follows for M ≥ 5. #716: 21/20 ≤ u_𝔏/2, 48.5 ≤ 64, 16 ≤ 24. #720: 2·21/20 ≤ u_𝔏/2, 4 ≤ 24.
- #288: u_𝔏 = 640(2^d + 8) = 15360, so 4·10⁴u_𝔏 = 6.144·10⁸.
- Since r29's repairs: #629-4 cites D2.7 15.8-1(6), (6-0) (D2.7 69e9e760040e). (6-0) is re-derived: 4(64ν + (3/4)ν/5832) ≤ 0.2566 at ν ≤ 1/1000, e^{0.26} < 2, and the link clause is #629-4's eighth. #288's 15.8-1(2-5) still gives u = 640(2^d + 8) and L ≥ 4·10⁴u. Pins: TL 8b44775cefa6, PC e72733f6404e, LF 4ad0e9992e08.
- Size: 18,434 characters of reviewed blocks (18,427 before the (6-0) citation); definition check 0 conflicts. No finding. A clean round is expected.

## Verdict: pc-links_a-20261106-r1

- One serious finding (F1) and five minor ones (F2 to F6); no fatal finding. The arithmetic (18.05, 0.22605, 0.208, 8832, 24, 1408, the budget 0.00225ν < ν/256) was checked and found correct. Not clean.

## Findings and repairs (links_a r1)

- F1 (serious; #629, #629-2, #255, #717 to #721). The referee asked whether a link's set in dom P is its network or the map's dependence set, the R_D ≤ 6LMR_k neighbourhood of #MD2.3.4.51-3. Re-derived from map #MD2.0.3.64 and #MD2.3.8.7, D26 7.4(a) and *The collar*, map #MD2.3.4.21-1, #MD2.3.4.32 to 33 and #MD2.3.4.51-3 to 5, and LFR II p.377 l.5 to 6, p.378 l.24 to 31 and p.389 l.10.
- F1, the field half. e_X is a number given the term's labels, so it has no field dependence, and R_D (a (𝐔, 𝐉)-margin for the tori) does not enter. So (H0) and X^{Cov} ⊆ S_g are untouched.
- F1, the label half. The R-operation sums X_c's labels inside 𝐓′_k(X_c). A cluster reads data on its network's 3M-neighbourhood and on the cutoff cubes meeting it. For n < k the step-n collar of X_c's labels stays in X_c, and Coll_k is fixed by Z_k. So a link that reads X_c's labels lies within 3M of X_c and meets X_c^∼ ⊆ its X′_r (R_k ≥ 3).
- F1, repair. #629 now uses the link's set X̂; new #629-0 to #629-0-2 hold the argument above. #629-2 defines X̂ as the closed-connected union of the π_n-cubes meeting the network, with the same counts. The second-class wording in D2.7 15.8 goes to the LF session.
- F2 (#629-2). The cube count now cites D26 7.4(a) and #509, the diameter map #MD2.3.4.46-1 to 2.
- F3 (#288). L₀ = 5000 is now cited at #MD2.4.6.16. The order is stated: L₀^× depends on d only, κ_s and M are fixed after L, and κ_D′ decreases in L. D2.7 15.8-1(2-5)'s "lower bound on L only" goes to the LF session.
- F4 (#629-4-1, #849). The link's part of |Ψ_g| in (6B) is paid by #629-4-1 (#724). D2.7 15.8's a°(X)/8 bounds the same factor per MR_k-cube, and (6B) does not use it. #849 now cites #724 and #629-4-1 for Ψ.
- F5 (#629-4-1). #661 and #762 are separate sums: the clusters of the gases Ξ^c, which hold no cross group (#660), and the first case's cross groups.
- F6. #629-0 names D2.7's 𝔏 apart from (R-member)'s relation (#247). #718 and #660 now say "interleaving". #281 now says "a factor at most u_𝔏", and #598 "one π_n-side".
- SHAs after the repairs: TL bf95d207391f (labels 9299985ab835). PC and the LF are unchanged.

## Pre-check: pc-links_b-20261106-r1 (first round)

- The revisions are named pc-links_a and pc-links_b (underscore), since the pre-check gate parses a part name without hyphens.

- Every line was read in full: #660 to #666, #723, #724, #729, #748, #751, #754 to #765, #777, #778, #795, #798, #826 to #835, #838, #844 to #844-9, #849, #859, #PC4.3, #PC4.4, #PC5.2, #PC5.2-3 to #PC5.2-5.
- Sum lemma (#876): 6/a at a = ν_rD/(1024M) is 6144M/(ν_rD); 12/a² at a = ν_rD/(1076M) is 13893312M²/(ν_rD)². #662: 4 gases × 2^d·4(ℓ₁ + ℓ₂)L^m cubes gives 2^{d+4}.
- Decay used once: c_F/2 to the payment (#727; in (6C) #802's 5·2^{d+2}ν_r ≤ c_F covers 160ν_r per D_P), c_F/4 to the interleaving entropy, c_F/8 each to the join positions (#758) and to the offsets or the separation (#754-1, #762). #661's clusters are a separate sum. Links: ν_r/2048 (offsets) + ν_r/4096 (positions) + Ψ ≤ ν_r/1024, and the separations take ν_r/512.
- #754-1: 4/34 ≤ 1/8, 8/(512·34) = 1/2176 ≤ 1/2048, 4.2/(34·512) ≤ 1/8. #759: (21/4)MC_jnε_k ≤ ν_r/4 under 24MC_jnε_k ≤ ν_r. #762: 1024·21/20 = 1075.2 ≤ 1076. #724: 32.5 + 276M ≤ 64 + 1280M. #795: (3/8)(ν_r/8)·6 = 9/32, and (6R_k + 3)/64 ≤ (R_k + 1)/8. #828: 21/5 + 21/20 = 21/4, 36.5 ≤ 64. #829: 21/4 ≤ u_𝔏/3. #835: (ν_r/4)D_P = (ν_r/256)·2^{d+2}D_P, as #849 counts it. #849: 2 + 1/256 + 3/80 = 2.041 ≤ 5/2.
- #844-2: 1/0.078 = 12.8 ≤ 13. #844-3: 4/3 ≤ 13. #844-4-1: λ_n − 1/32 ≥ 15/16. #844-5: C_att ≥ 2e^{−a}(1 + 1/a) at D ≥ 1. #844-8: (33/32)·1.5⁸ = 26.4 < 5000. #844-9: S^R (#774) contains Σϑ_k.
- Since links_a r1's repairs: #660 now says "joined by overlaps and by interleaving" (wording only), and #849 cites #724 and #629-4-1 for the links' Ψ part, which #724 already pays within #629-4-1's quarter (C_Ψ′e^{−p₀/2}(2^d + 8M)ℓ_P, small for small g_k). The context lines #629-0 to #629-4-1 now say that a link enters by X̂ with the same counts, and that #661 and #762 are separate sums. No bound of this packet moves. Pins: TL bf95d207391f, PC e72733f6404e, LF 962274040a17, table 8e227609f36c. The LF and table changes since 4ad0e9992e08 (#4.48.1 to #4.567 and #5.49-1, and #T4.43 without "times e³") are cited by neither note. Size 19,099 characters, definition check 0 conflicts. A clean round is expected.
- Since r29's repairs, before links_a r1: no line in this packet changed. #850, context, cites 15.8-1(4-1), (6-2), which still state ŷ_g and its payment. The PC lines changed since (#PC4.14.4-4.5.4-3-2, -3-3) are outside the packet. Pins: TL 8b44775cefa6, PC e72733f6404e, LF 4ad0e9992e08.
- Size: 19,086 characters of reviewed blocks; definition check 0 conflicts. No finding. A clean round is expected.

## Verdict: pc-links_b-20261106-r1

- No fatal or serious finding; nine minor ones (m2 to m8, m10, m11), all wording or citation. Every allocation and inequality the packet states was checked and found correct (1024, 1076, 2048, 4096, c_j, C_jn, C^R, C_att, the sum lemma's 6144 and 13893312). Not clean.

## Findings and repairs (links_b r1)

- m3 (#629-4-1). (6C) uses the links' quarter as (6B) does (#849, #854). The list now reads "in (6B) and (6C) (#724, #754, #758, #849, #854)", and neither uses D2.7 15.8's a°(X)/8 bound. A link's polymer lies in one group, so no part is used twice.
- m10 (#859, also #258). 1408u_𝔏 ≤ 4096L needs L ≥ 0.344u_𝔏, which L₀ = 5000 does not give. Both lines now cite L ≥ L₀^× (#288).
- m2 (#844). #843's ν_r/10 is in the inequality: (ν_r/10)(σ(W) + 1) ≤ (ν_r/5)σ(W) by σ(W) ≥ 1 (D2.6 closure 5.2 (T0)), and ½ + 1/5 + ϑ_k/4 ≤ 1.
- m5 (#729, #742, #755, #661). The name "interleaving entropy" is gone. #729 calls e^{−(c_F/4)D_P} a reserve, which *The rooted sum* holds with in its summand. #742 lists the summand's polymer factors: *The payment*, *Joins* and *Join count* (#754-1, #758) and the reserve, c_F per unit of D_P in all. #755 cites that list. In #661 the other half of c_F carries the rooted sum's reserve and joins' factors. #742 was 995 characters, so it is split at sentence boundaries into #742, #742-1 (the parts' factor) and #742-2 (C_gr).
- m11 (#732, #753, #754). #732 says "in *First case* (#762)". #753 and #754 name the two kinds of join by #752's words ("At a bond b of a span in g holding a slot of P′", "At a slot b of g in span(P′)") instead of "first case" and "second case".
- m4 (#723). The links' parts cite #629-4–#629-4-1.
- m7 (#PC5.2-5). The source's age is K′ − j or K′ − j + 1, which the factor L covers.
- m8 (#661). 15.3's amplitude bounds the group activities c_gΠ_{P∈g}F(P) (D2.7 15.4, re-read: "the group activities bounded by (ĉ₁)^{#components}e^{−κ(size)}"), so C^R needs no constant for c_g.
- m6 (#849). |Ψ_g| ≤ O(1)ĉ₁#cubes_k(hull g), ĉ₁ := e^{3+a_k}e^{−p₀(g_k)}, as D2.7 15.6 prints it (D2.7 15.3 for ĉ₁).
- SHAs after the repairs: TL c4fcd4085c14 (labels 9f51b9146733, 1107 tags), PC 255bf034b9af (labels 080502dd5c82).
- To LF (04:59): links_b r1 is done, so the 15.8 edits can go in; m3 and m10 explained. From LF (05:0x): D2.7 87d77709acc7 (was 69e9e760040e). Line 191 (15.8) now has e_X a number given the labels with X̂ (#629-2), the reading links meeting X_c^∼ (#629-0-2), the factorisation over the X′ and the X̂, and "X̂ meets at most 2^d#π_n(X̂) ≤ 2^{d+5}a°(X)/ν MR_k-cubes". Line 223 (15.8-1(2-5)) cites #288. Re-derived: #π_n(X̂) ≤ σ_n(X) = 32a°(X)/ν (#629-2), and ε·2^{d+5}a°/ν = a°/8 at ε = ν/2^{d+8}. Second-class labels are summed by 𝐓′_k(Y_i) from outside the bracket ((1.72)), as #629-0-1 has it.

## Pre-check: pc-links_a-20261107-r2 (full round, prior r1)

- Changed against r1's snapshot inside the packet: #258, #281, #288, #598, #629, #629-0, #629-0-1, #629-0-2 (new), #629-2, #629-4-1, #718. The context lines #660, #661, #723, #729, #732, #742 to #742-2, #753 to #755, #844, #849, #859 and PC #PC5.2-5 also changed (links_b r1's repairs). Each was re-read.
- The whole part was read before this full round: #253 to #258, #271, #281, #285, #288, #491, #520, #538, #570 to #572, #583, #598, #599, #629 to #629-5, #683, #690 to #721. #714: links' cubes ≤ 2^dℓ_P (#629-2). #716: 2^d = 16 ≤ 24 = u_𝔏λ_𝔏. #720: 2·2ℓ_P = 4ℓ_P ≤ 24ℓ_P, 21/10 ≤ u_𝔏/2. #258: 1408u_𝔏/4096 = 0.344u_𝔏 ≤ L₀^×.
- F1: #629-0 to #629-0-2 against map #MD2.0.3.64, #MD2.3.8.7, #MD2.3.4.21-1, #MD2.3.4.32 to 33, #MD2.3.4.51-3 to 5, D26 *The collar* and *Where their groups live*, and p.377 l.5–6, p.378 l.24–31 and p.389 l.10. D2.7 15.8 now says the same (87d77709acc7).
- #629-0 now writes "with n = n(X) ≤ k the step that made X", since the definition gate read "n := n(X)" as a second definition of n.
- Pins: TL aa8f68c27da3 (labels 9f51b9146733), PC 255bf034b9af, LF e873ea0df345 (labels 93851bc1cc55), table 8e227609f36c, D2.7 87d77709acc7. The LF changed since 962274040a17 only in #4.563-2 and #4.563-2.1 (VAR's ∇ citations), and neither note cites them. Size 20,755 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r2

- No fatal or serious finding. r1's F1 to F6 are resolved. Two minor findings (N1, N2) and one remark (N3). All the arithmetic was checked and found correct. Not clean.
- How the pre-check missed N2: it took D26 7.4(a)'s #cubes_n(X) to count the π_n-cubes meeting the network, without checking that count's definition (map #MD2.4.3.1: the constituents' cubes only).

## Findings and repairs (links_a r2)

- N1 (#629-0-2). "Within 3M of X_c" needs each cutoff cube carrying X_c's labels to lie in X_c. Re-derived from CRE p.246 l.24–27, p.254 l.54, p.245 l.33–37, p.256 l.21–22 and D2.7 15.4(ii). A step-n cutoff cube is an LM₂R_n-cube of T_{L^{−n}}, and LM₂R_nL^n divides MR_kL^k (powers of L, M₂ < M, R_nL^n ≤ R_kL^k). So the cube lies in one MR_k-cube, and X_c is a union of MR_k-cubes. This is the new #629-0-3, split off from #629-0-2 for length.
- N2 (#629-2, through #629-5, u_𝔏 and L₀^×). The arc hull I(𝒢) enters σ only through n/M, so "#π_n(X̂) ≤ σ_n(X)" fails as stated. Re-derived from map #MD2.3.4.46-1 to 3, #MD2.4.3.1, #MD2.2.6.119, TL #628, #750 and #509.
  - X̂ is now the network plus one lattice path of ℓ^∞-diameter ≤ M per incompatible pair in a spanning tree. It is connected, with diam ≤ 2Mσ_n(X) (unchanged).
  - Its cubes are ≤ Σ_𝒢(#_n + 2^d(n_n/M + 2) + 2^d) ≤ 2^{d+2}σ_n(X) (#629-2-1).
  - So u_𝔏 := 640(2^{d+2} + 8) = 46080, with λ_𝔏 = 1/640 kept, and L₀^× = 1.8432·10⁹. The 2^dℓ_P terms are now 2^{d+2}ℓ_P in #710, #714, #716, #724, #828 and #829.
  - Every inequality in u_𝔏 still holds: #254's 18.05; #257's ratio is now 0.22598 ≤ 0.227; #696's 0.208; #583; #598; #716's 64 ≤ 72; #720's 4 ≤ 72; #829's 21/4 ≤ u_𝔏/3. The links' budget (#629-4) does not involve u_𝔏.
- N3 (#288). C_box ≥ 4A_E (map #MD2.4.12.6-1) is listed among the constants fixed after L.
- To LF (05:3x): D2.7 l.3, 15.8 (l.191: X̂'s definition, the MR_k-cube count 2^{d+2}σ = 2^{d+7}a°/ν with ε := ν/2^{d+10}, the attachment-cube count with O(1)c₁2^{d+2} ≤ ν/256, and #629-0-2 to #629-0-3), 15.8-1(2-4) and (2-5) (u = 640(2^{d+2} + 8)), and #T4.42. Pending.
- SHAs after the repairs: TL b06dcee33fc2 (labels dde7d94a4736, 1109 tags). PC 255bf034b9af is unchanged.
- Next: links_a r3 (full) and links_b r2 (full; rebuilt, since #724, #828 and #829 changed), after the LF session's edits.

## Pre-check: pc-links_a-20261107-r3 (full round, prior r2)

- Changed against r2's snapshot inside the packet: #288, #629-0-2, #629-0-3 (new), #629-2, #629-2-1 (new), #629-5, #710, #714, #716. The context lines #724, #828 and #829 also changed. Each was re-read.
- Every use of the links' cube coefficient was grepped: 2^dℓ_P, 2^dσ, (2^d + 8), 15360 and 6.144 no longer occur in TL or PC. u_𝔏 enters numerically only in #254, #257, #583, #598, #696, #716, #720, #829 and #859, and each still holds at 46080 (see the links_a r2 repairs). Symbolic uses (#491, #572, #844-5's C_att) carry no number.
- #629-2-1's count: per group, # + 2^d(n/M + 2) + 2^d ≤ 2^dσ(𝒢) + 3·2^d ≤ 2^{d+2}σ(𝒢), with σ(𝒢) ≥ 1. The ⌈t/M⌉ runs of ≤ M consecutive bonds each have ℓ^∞-diameter ≤ M by #750's two cases, so each meets ≤ 2^d blocks under #628's site convention.
- #629-0-3's pins were re-read: CRE p.246 l.24–27 (the MR_1- and LM₂R_1-partitions of T_{L^{−1}}), p.254 l.54 (S_j unions of LM₂R_j-cubes in T_{L^{−j}}), p.245 l.33–37 (M = L^m, M₂ = L^{m₂}, M₁ < M₂ < M), p.256 l.21–22 (Ω_j, Λ_j unions of MR_j-cubes).
- #629-0-3 covers the cutoff cubes of every step j ≤ n, the old insertions' included, as #629-0-1's dependence set does.
- From LF (05:4x): D2.7 0358d315f174, table d4776667c9bd (labels 6e94c992cd11), LF unchanged at e873ea0df345. Checked: l.3 and 15.8-1(2-5) have u = 640(2^{d+2} + 8). l.191 has X̂ as the network with paths, the reader sentence citing #629-0-2–#629-0-3, the attachment cubes ≤ 2^{d+2}σ with O(1)c₁2^{d+2} ≤ ν/256, and 2^{d+7}a°/ν MR_k-cubes with ε = ν/2^{d+10} (ε·2^{d+7}a°/ν = a°/8). 15.8-1(2-4) has 2^{d+2}σ and 2Mσ. #T4.42 has (2^{d+2} + 8)σ.
- Pins: TL bcfb035c3ced (labels 7b50be473bdf), PC 255bf034b9af, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 21,685 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Pre-check: pc-links_b-20261107-r2 (full round, prior r1)

- Changed against r1's snapshot inside the packet: #661, #723, #729, #742 to #742-2 and #753 (added to the extracts, since they changed and #755 cites them), #754, #755, #844, #849, #859, #PC5.2-5. The context lines #258, #629-0 and #629-4-1 changed too. Each was re-read.
- The whole part was read before this full round, including #664 to #667, #777, #778, #795, #798, #826 to #838, #844-1 to #844-9, #845, #PC4.3 to #PC4.4-1.2. #729's allocation c_F/2 + c_F/4 + c_F/8 + c_F/8 = c_F is what #742 lists, and #755 cites it. #844: (ν_r/10)(σ + 1) ≤ (ν_r/5)σ at σ ≥ 1, and ½ + 1/5 + 1/128 ≤ 1. #835: (ν_r/8)(21/10) = 21/80. #859 and #258: 1408/4096 = 0.344 ≤ 4·10⁴.
- After links_a r2's N2: #724 now has (2^{d+2} + 8M)ℓ_P, small for small g_k within the links' quarter. #828 and #829 now have (2^{d+2} + 8)ℓ_P = u_𝔏λ_𝔏ℓ_P = 72ℓ_P. #844-5's C_att = 2(1 + 32u_𝔏M/ν_r) is symbolic in u_𝔏, and #859 holds for L ≥ L₀^×. The first build (TL aa8f68c27da3) was removed unlaunched.
- Pins: TL bcfb035c3ced, PC 255bf034b9af, LF e873ea0df345, table d4776667c9bd (labels 6e94c992cd11), D2.7 0358d315f174, the same as links_a r3. Size 20,663 characters of reviewed blocks, definition check 0 conflicts. It launches after links_a r3 reports, provided that round leaves these lines unchanged. A clean round is expected.

## Pre-check: pc-rstep-20261107-r30 (full round, prior r29)

- Changed against r29's snapshot (tagged-line diff over the packet's ranges, nothing removed): TL #812, #812-1 (new), #814, #815.2, #815.2-1 (new), #816, #816-1 (new), #849 (links_a F4's Ψ citation and links_b m6's ĉ₁, D2.7 15.6 and 15.3); PC #PC4.14.4-4.5.4-3-2, #PC4.14.4-4.5.4-3-3. Each was re-read in full.
- #812 to #812-1 against p.389 l.27 to 28, (1.95) to (1.97) and p.390 l.1. Bałaban prints the dichotomy: X′ either contains one of the Y_i, and then q starts at 0 with c_0 = α^{1/3}, or it is disjoint from ∪Y_i, and then q ≥ 1. So "meets ∪Y_i, so contains some Y_i" is printed, not inferred. The q-parts on one X′ overlap, so the polymer sum is unchanged, and each part is bounded by (1.95)'s positive sum over q.
- #814: 8^{1/3} = 2; the factor left per q = 0 part is 4(64ν_r + (3/4)ν_e) ≤ 0.2566 at ν ≤ 1/1000, ν_e ≤ ν/5832, e^{0.26} < 2 (D2.7 15.8-1(6-0)). The cluster's e^{(3/8)ν_e} ≤ 2 is in C_Ψ″ (15.8-1(6-3)). The root is a fixed cube of the first Y_i contained, which exists by #812-1. (8α)^{1/3} ≤ 1.
- #815.2: each term of w^Ψ_c has its payer: cubes off ∪Y by a_V/2 and (1.89)'s margin; D^∪_P's length by #727, #806; 4R_k + 92 at q ≥ 1 by #645; 4 at q = 0 into #814; links by #629-4; the Y_j cubes carry none. #815.2-1: Σ_cy_c ≤ 2C_Ψ″e^{2C_Ψ″} = m^w_Ψ, using |e^z − 1| ≤ |z|e^{|z|}.
- #816 to #816-1: e^{κ101^d} is per Y_i and term for the (6B) and (6C) polymers (#818); the q = 0 parts lie in slotless polymers (15.4(i)) and are summed as in (1.95) to (1.97).
- PC -4.5.4-3-2 cites 15.8-1(1-1) to (1-2), which hold the R-groups, D_g = D̂_g[𝒲_g], the norm ≤ B(g), hull_c(g) and the open slots. PC -4.5.4-3-3 cites #286, which lists C_δc̄S_R + (1 + C_ϑ + C_attC_y)S^R ≤ log 2.
- The LF session's m-c edit is in: #T4.43 and LF #5.49-1 no longer carry "times e³". Neither note's r30 lines cite LF #5.49-1. #T4.43 was re-read against #814–#817 and agrees.
- Re-run after links_a and links_b were done (07 Nov, 08:30). The diff against r29's snapshot, in r30's ranges, adds TL #849 and #849-1 to the list above.
  - #849 now pays the small members at 3ν_r/80 per unit of D_P (#857). The rate is ν_r + ν_r + ν_r/256 + 3ν_r/80 ≈ 2.041ν_r ≤ (5/2)ν_r.
  - #849-1 pays the links' part of Ψ by O(1)e^{−p₀(g_k)/4}(2^{d+2} + 8M)ℓ_P, with N(Y_i)e^{−p₀/2} ≤ e^{−p₀/4} at second-class cubes and #724's count. This lies within #629-4-1's quarter for small g_k.
- Context changes cited by r30's lines were re-read: #806 (its list includes *Joins*), #629-4 (C_box = 2916 by table #T4.44), #844-7, #724. D2.7 971428523236 was re-read at 15.8-1(1-1), (1-2), (2-2), (6), (6-0), (6-3) and (3-1) (#572-1).
- New blocks under review:
  - #253–#258, moved from links_a, where r6 to r9 found them CORRECT. #256 was split, with no change of content.
  - #288, #628-1 and #629-0-1–#629-0-1-1, links_a r9's two remarks. C_box = 2916 (table #T4.44, re-derived from map #MD2.4.12.6-1, #MD2.4.13.3-2, #MOMGD.14-4). The step-1 halo M(1/2 + C_boxL) fine bonds = M(1/(2L²) + C_box/L) step-2 bonds < M for L ≥ 2C_box.
- LF e873ea0df345: none of the LF tags changed since r29 is cited by r30's packet. Table ad3071f9d866: of the changed rows #T4.42, #T4.43 and #T4.44, the packet cites #T4.44, which agrees with #288.
- Size: 23,009 characters of reviewed blocks, definition check 0 conflicts. Its first check flagged C_box (TL #288 against #T4.44); #288 now cites the row.
- Pins: TL dea57b5d62ba (labels 149b0f46ef44), PC 47562cd8272f (labels 080502dd5c82), LF e873ea0df345, table ad3071f9d866 (labels 16fb990d788d), D2.7 971428523236. The whole part was read this session. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r3

- No fatal or serious finding. r2's N1, N2 and N3 are resolved, and every inequality at d = 4 was rechecked and holds. Two minor findings (m1, m2) and two remarks (R1, R2). Not clean.

## Findings and repairs (links_a r3)

- m1 (#285, #572). D2.7 15.8-1(3-1) gives the R-made fixed member 𝒟(𝒴) at most 420uMσ^𝒟 positions, so its (T0) condition has 420 in place of 170, and #285 named only #572's. Re-derived from D2.7 15.8-1(2-5) to (3-1), TL #557, #566 to #568, and D26 (T0) (fixed members are data, not vertices; a dev 𝒟(𝒴) is a vertex). Repairs:
  - #572 now covers the insertions other than 𝒟(𝒴), and names 𝒟(𝒴) among the neighbours whose windows reach D. Its windows follow the same map l.622 rule as #557, with #566's units at u_𝔏.
  - The new #572-1 gives 𝒟(𝒴)'s condition, with 420 in place of 170, which implies #572's.
  - #285 and #859 cite #572-1. #570 and #700 list 𝒟(𝒴)'s u = u_𝔏 (15.8-1(2-5)).
- m2 (#629-0-3). CRE p.256 l.21–22 covers Ω_j and Λ_j, not X_c. The line now runs: X_c is a component of Z ⊆ Z_k (LFR I p.177 l.33–34, re-read: Z is the union of a class of components of Z_k), and Z_k = Λ_kᶜ is a union of MR_k-cubes, as Λ_k is.
- R1 (#629-0-2). The sets derived from the labels, other than the collar, were not covered. Re-derived from CRE p.268 (3.16), p.269 l.4–16 ((3.20), R′ as the LMR-cubes meeting R, and the parallelepiped rule), and D26 *Where their groups live*. A step-n object reads the step-j sets, j ≤ n (map l.3110, l.3258).
  - These sets are built from label sets by at most two layers of LMR_j-cubes (six π_n-layers for the collar) and by parallelepiped hulls.
  - Each layer or hull lies in Λ_jᶜ (the collar in Ω_{n+1}ᶜ), hence in Z_k, since Λ_k ⊆ Λ_j ⊆ Ω_j^{∼−2} ∩ (R′_j^∼)ᶜ for every labelling.
  - So a cube added by touching a part in X_c, or a hull of a component meeting X_c, is closed-connected to X_c inside Z_k, and so lies in X_c.
  - #629-0-2 is rewritten, and #629-0-2-1 is new (split for length). It covers n = k too, and only the collar keeps the n < k proviso.
- R2 (#629-2-1). Dropping #750 alone would leave the paths without a cited count, since #628 counted only lattice paths of at most M steps, and a path of ℓ^∞-diameter M can have up to dM steps.
  - #628 now counts at most 2^d cubes for any set of ℓ^∞-diameter ≤ M, two in each coordinate, since M + 1 consecutive sites meet at most two blocks of M.
  - It is split into #628 and #628-1 for length. #629-0-2-1 and #629-2-1 cite #628-1, and #816 still cites #628 for the side M.
  - #629-2-1 now states t₁ + t₂ ≤ n_n(𝒢), giving at most n_n/M + 2 runs.
- #700 was split at "The proof is by induction" (#700-1) for length.
- Tag diff against r3's snapshot: 285, 570, 572, 572-1 (new), 628, 628-1 (new), 629-0-2, 629-0-2-1 (new), 629-0-3, 629-2-1, 700, 700-1 (new), 859. Nothing removed.
- No citation elsewhere needs to change. D2.7 l.191 cites #629-0-2–#629-0-3, which covers -2-1, and D2.7 15.8-1(3-1)'s "two-loops #572's condition with 420 in place of 170" still reads correctly. The LF session is told.
- SHAs after the repairs: TL fabd9611eb50 (labels 326462d2768c, 1113 tags). PC 255bf034b9af is unchanged.
- Queued: found in my full read of the r4 part. It waits because TL is frozen while links_b r2 runs. #629-0-2 to #629-0-2-1 treat only the step-n collar, but old insertions made at steps j < n carry step-j collars.
  - Repair: "the step-j collars, the π_j-cubes within 6 layers of Λ_jᶜ", lying in Ω_{j+1}ᶜ ⊆ Λ_kᶜ for j < k (Λ_k ⊆ Λ_{j+1} ⊆ Ω_{j+1}), and "at j = k the collar is fixed by Λ_kᶜ = Z_k".
  - links_a r4 (built for measurement: 23,799 characters, 0 conflicts) is rebuilt after this edit.

## Pre-check: pc-links_b-20261107-r2, rebuilt after links_a r3

- The only change inside the packet is #859, which now cites #571–#572-1. The context lines #572, #572-1 and #629-0-x changed with links_a r3's repairs. Each was re-read. The earlier build at TL bcfb035c3ced was removed unlaunched.
- Pins: TL fabd9611eb50, PC 255bf034b9af, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 20,665 characters of reviewed blocks, definition check 0 conflicts. A clean round is expected.

## Verdict: pc-links_b-20261107-r2

- No fatal or serious finding. r1's m2 to m8, m10 and m11 are resolved, and every constant and inequality was rechecked and holds. Three minor citation and wording findings (n1, n2, n3). Not clean.

## Findings and repairs (links_b r2)

- n1 (#755). The rooted sum's per-cube sum was credited to *The free decay* (#636), which covers only the D_P factors. The links' factors in the summand (weight and extent, the offsets' ν_r/2048, the positions' ν_r/4096, and Ψ) are paid from the a°(X)/4 that D2.7 15.8 leaves free in 15.3's sum (l.191). #755 now names both sources (#629-4–#629-4-1).
- n2 (#849). D2.7 15.6 (l.183, re-read) bounds Ψ with N(Y_i)ĉ₁ ≤ O(1)e^{−p₀(g_k)/4} in place of ĉ₁ at the cubes of a second-class Y_i, and #849 left this out. (6C)'s Ψ constant is O(1)ĉ₁, not #724's C_Ψ′.
  - #849 now quotes the qualification.
  - The links' sentence is split off as #849-1. It gives their Ψ part as O(1)e^{−p₀(g_k)/4}(2^{d+2} + 8M)ℓ_P, #724's count with (6C)'s constant, which is small for small g_k inside ν/4096.
  - #629-4-1 cites #849-1. The ranges #849–#850 in TL #829, PC #PC4.14.4-4.5.4-3-x, D2.7 l.243 and #T4.42 cover -1, and D2.7 l.237's "#849" is the rate, which stays in #849.
- n3 (#661). "The other half of c_F carries the reserve and the joins' factors of *The rooted sum*" read as one shared budget. It now says that these gases hold no cross group and no join, and that the rooted sum is a separate sum with its own split of c_F (#729).
- Queued from the links_a r4 read, now applied: #629-0-2 to #629-0-2-1 cover the step-j collars, j < k, which lie in Ω_{j+1}ᶜ ⊆ Λ_kᶜ (Λ_k ⊆ Λ_{j+1} ⊆ Ω_{j+1}). The step-k collar is fixed by Z_k.
- Tag diff against links_b r2's snapshot: 629-0-2, 629-0-2-1, 629-4-1, 661, 755, 849, 849-1 (new). Nothing removed.
- SHAs after the repairs: TL f8d1d3d6e5c1 (labels 81ec194d1e8f, 1114 tags). PC 255bf034b9af is unchanged.
- Next: links_a r4 (full), then links_b r3 (full). For each, two consecutive clean rounds are still needed, the second a full one.

## Pre-check: pc-links_a-20261107-r4 (full round, prior r3)

- Changed against r3's snapshot inside the packet: #285, #570, #572, #572-1, #628, #628-1, #629-0-2, #629-0-2-1, #629-0-3, #629-2-1, #629-4-1, #700, #700-1. The extracts now include #628 to #628-1, #572-1 and #700-1. The whole part (23,807 characters) was read in full before this full round, which found the step-j collar point, now repaired.
- Every citation of a touched tag was grepped in TL, PC, D2.7, LF and the table:
  - #572's: #258, #285, #859 and D2.7 15.8-1(3-1). D2.7's "with 420 in place of 170" stays correct.
  - #628's: #629-0-2-1 and #629-2-1 moved to #628-1; #816 stays at #628 for the side M.
  - #629-0-x: D2.7 l.191's range covers -2-1.
  - #849: only #629-4-1 moved to -1.
- Checks:
  - 420u_𝔏 + 196u_𝔏²/c_w ≥ 170u_𝔏 + 196u_𝔏²/c_w, so #572-1's condition implies #572's.
  - M + 1 consecutive sites meet at most two blocks of M, so a set of ℓ^∞-diameter ≤ M meets at most 2^d.
  - ⌈t₁/M⌉ + ⌈t₂/M⌉ ≤ n_n/M + 2.
  - Λ_k ⊆ Λ_j ⊆ Ω_j^{∼−2} ∩ (R′_j^∼)ᶜ holds for the final Λ_j, since p.269's parallelepipeds only enlarge Λ_jᶜ. A cube touching a closed cube of X_c inside Z_k lies in X_c, by closed-connectedness (#628-1).
- Pins: TL f8d1d3d6e5c1 (labels 81ec194d1e8f), PC 255bf034b9af, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 23,807 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r4

- No fatal or serious finding. r3's m1, m2 (apart from m2′), R1 for the listed sets, and R2 are resolved. Four minor findings (m1, m2′, m3, m4). Not clean.

## Findings and repairs (links_a r4)

- m1 (#629-0-2 to #629-0-2-1). The list of derived sets was argued exhaustive by outward layers only, and CRE's Λ_j⁰ (p.259 l.30–31) moves cubes inside Λ_j. Instead of extending the list, the two lines now give a locality argument.
  - #629-0-2 names the step-j label sets (Ω_jᶜ, Z_j with p.269's parallelepipeds, R_j ⊆ S_j ⊆ Λ_jᶜ). It says that every derived set (CRE (3.16)'s domain and cutoff cubes, S_j, R′_j, Λ_j⁰, Coll_j) is given at each point by the label sets within one LMR_j-layer of it.
  - #629-0-2-1: for j < k a labelled point lies in Λ_jᶜ, more than three LMR_j-layers from Λ_k. This holds because Λ_k ⊆ Ω_{j+1}, the 6 LMR_{j+1}-layers about Λ_jᶜ lie in Ω_{j+1}ᶜ (D26 (G1), re-read), and an LMR_j-layer is at most two LMR_{j+1}-layers (CRE (2.9), R_j ≤ (L+1)R_{j+1}, re-read). For j = k, Z_k is fixed, and Ω_kᶜ and R_k are read only within (Ω_kᶜ)^∼ and R′_k, both in Λ_kᶜ by CRE (3.20). So a point that reads a label of X_c is joined to it inside Z_k and lies in X_c (#628-1).
  - Coll_j's 6 π_j-layers (side 6M) lie within one LMR_j-layer, since LR_j ≥ 6.
- m2′ (#629-0-3). It now reads "X_c is a component of Z, a union of components of Z_k = Λ_kᶜ (LFR I p.177 l.33–34)". The compatibility of the partitions is cited as p.245 l.33–40 (l.38–40 re-read). The line is now 594 characters.
- m3 (#628). It now reads "LFR II's d_{k,∪Y_i}(X′_r), the relative size (1.67) with ∪_iY_i in place of Z ((1.93), p.388 l.29)", matching #806's use.
- m4 (#599, #491). #599 adds "and 420u_𝔏Mσ^𝒟 for D2.7's 𝒟(𝒴) (#572-1)". #491's count adds "420u_𝔏Mσ(D) for D2.7's 𝒟(𝒴), #572-1". #285 already imposes the stronger condition, so no bound changes.
- Tag diff against r4's snapshot: 491, 599, 628, 629-0-2, 629-0-2-1, 629-0-3. Nothing removed or added. Citers: D2.7 l.191's range #629-0-2–#629-0-3 is intact. The N-loops note's #599 citation is unaffected (count extended, not changed).
- SHAs after the repairs: TL 39604481738d (labels 8605765bdb15, 1114 tags). PC 255bf034b9af is unchanged.
- Next: links_b r3 (full), then links_a r5 (full).
- Queued for links_a r5, found while writing its spec; TL is frozen during links_b r3. #629-0-2-1's "an LMR_j-layer is at most two LMR_{j+1}-layers (CRE (2.9))" leaves the unit conversion implicit. Cube sides scale as R_jL^j (#629-0-3), and R_jL^j ≤ 2R_{j+1}L^{j+1} follows from R_j ≤ (L+1)R_{j+1} (CRE p.256 l.15, n − m = 1) and (L+1)/L ≤ 2. The citation becomes "(R_jL^j ≤ 2R_{j+1}L^{j+1}, CRE (2.9))".

## Pre-check: pc-links_b-20261107-r3 (full round, prior r2)

- Changed against r2's snapshot: in the packet, #629-4-1 (context), #661, #755, #849, #849-1 (new, extract extended); outside it, links_a r4's #491, #599, #628, #629-0-2–#629-0-3 (packet pc-links-a). The whole part (21,064 characters) was read in full before this full round.
- Arithmetic rechecked:
  - #754-1: 4/34 ≤ 1/8, 8/(512·34) ≤ 1/2048, 4.2/34 ≤ 1/8.
  - #758: 20MD_P positions under 160MC_jnε_k² ≤ c_F, and the links' 8Mℓ_P within ν_r/4096.
  - #759: (21/4)MC_jnε_k² ≤ (ε_k/4)ν_r since 21 ≤ 24.
  - #762: 1024·21/20 = 1075.2 ≤ 1076.
  - #666 and #778: 6144/1024 = 6 and 13893312 = 12·1076².
  - #724: 32.5 + 276M ≤ 64 + 1280M.
  - #795: 3(2R_k + 1)/64 ≤ (R_k + 1)/8.
  - #849: ν_r + ν_r + ν_r/256 + 3ν_r/80 ≤ (5/2)ν_r, and (ν_r/4)D_P = ν_r/256 per unit of 2^{d+2}D_P at d = 4.
  - #844-2 and #844-3: 1/0.078 ≤ 13 and 4/3 ≤ 13.
  - #844-4-1: 31/32 − 1/32 = 15/16.
  - #844-8: (33/32)·1.5⁸ < 27.
  - #PC5.2-5: a^cr_E ≤ ν_r/(1024M) and D ≥ 1.
- Budget use is once each:
  - offsets ν_r/2048, positions ν_r/4096 and Ψ ≤ ν_r/4096 come from the quarter ν_r/1024;
  - the separations, at ν_r/512 per unit of ℓ, are used in #661's sum and in the rooted sum's first case (#762), separately;
  - c_F/2 goes to the payment, c_F/4 to the reserve, and c_F/8 each to the join positions and to the offsets or separation (#729).
- Pins: TL 39604481738d (labels 8605765bdb15), PC 255bf034b9af, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 21,064 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_b-20261107-r3

- No fatal or serious finding. r2's n2 and n3 are resolved, and n1 is resolved for the links. Two minor findings (m1, m2), neither changing a bound, and one remark on #PC4.4. Not clean.

## Findings and repairs (links_b r3)

- m1 (#755). The payers of the summand's factors left out *The payment*'s factor on #π_k(B_P), which *The volume* pays (#725's a_V/2 per cube, #726's (1.89) margin; both re-read). #755 now lists it: "those in #π_k(B_P) by *The volume* (#725–#726)".
- m2 (#795).
  - σ_g holds λ_𝔏ℓ_P through π(P) (#691), so (9/32)ν_rσ_g held a link part that #629-4's ν_rλ_𝔏 + 4ν_e does not list.
  - #720's first bound has its ℓ-part separately as 4MΣℓ_P. Its other terms (2ΣD_P, (21/20)Σσ_×, (21/10)Σσ_s) are at most 6(σ_g − λ_𝔏Σℓ_P), since 2 ≤ 6·2^{d+2}, 21/20 ≤ 6, and 21/10 ≤ 6·½.
  - So #795 now bounds the diameter by 6M(σ_g − λ_𝔏Σ_Pℓ_P) + 4MΣ_Pℓ_P and charges (9/32)ν_r(σ_g − λ_𝔏Σ_Pℓ_P). The links' only extent term is (3/2)ν_eℓ_P ≤ 4ν_eℓ_P (#629-4).
  - Consumers are unaffected: #798's 2 + 9/32 ≤ 5/2 per unit, and #799's (9/32)ν_r·½σ(D).
- Remark (#PC4.4). #PC4.4 now states â_* ≥ min(a_×, 2c_w/M, a^cr_E) by N_s ≥ 2 (#749), uniformly in the volume.
- Queued item applied: #629-0-2-1's conversion "(R_jL^j ≤ 2R_{j+1}L^{j+1}, CRE (2.9))", 600 characters.
- Tag diff against r3's snapshot: TL 629-0-2-1, 755, 795, and PC PC4.4. Nothing removed.
- SHAs: TL 7853159b46d5 (labels 70ae4168d982, 1114 tags), and PC 47562cd8272f (labels 080502dd5c82, unchanged).
- Next: links_a r5 (full), then links_b r4 (full).

## Pre-check: pc-links_a-20261107-r5 (full round, prior r4)

- Changed against r4's snapshot inside the packet: #491, #599, #628, #629-0-2, #629-0-2-1, #629-0-3. Outside it: #755, #795, and PC #PC4.4 (packet pc-links-b).
- The full read before launch found one more point, repaired here. #629-0-2 named R_j ⊆ S_j ⊆ Λ_jᶜ as label sets, citing p.378 l.24–31, which prints only {Ω_jᶜ ∩ X, Z_j ∩ X}.
  - Re-read: CRE (3.16) (p.268 l.18–21) sums over R_{k+1}. CRE (3.20) (p.269 l.8–10) defines S_{k+1} = (Ω_{k+1}∖Ω_{k+1}^{∼−1}) ∪ R_{k+1}.
  - #629-0-2 now names the large-field sets R_j ⊆ R′_j ⊆ Λ_jᶜ of CRE (3.16)'s sums, and lists S_j = (Ω_j∖Ω_j^{∼−1}) ∪ R_j and R′_j among the derived sets (CRE (3.20)).
  - The locality argument needs only that every label lies in Λ_jᶜ, so it is unchanged. S_j ⊆ Λ_jᶜ, since Ω_j∖Ω_j^{∼−1} ⊆ (Ω_jᶜ)^∼.
- Lines: #629-0-2 is 593 characters, #629-0-2-1 is 600, and #629-0-3 is 595.
- Citers: D2.7 l.191's range is intact. The N-loops note's #599 is unaffected.
- Constants rechecked:
  - #629-4: ν/640 + ν/1458 < ν/256.
  - #254: 18.05 ≤ u_𝔏.
  - #257: 416,532,240/1.8432·10⁹ ≤ 0.227.
  - #583: 414·64/3 = 8832.
  - #598: 24u_𝔏 ≤ L₀^×.
  - #696: 0.208 and 0.208 ≤ 0.21.
  - #716: 48.5 ≤ 64.
  - #629-2-1: #_n + 2^dn_n/M + 3·2^d ≤ 2^{d+2}σ_n.
  - #629-0-2-1: 6 LMR_{j+1}-sides ≥ 3 LMR_j-sides by R_jL^j ≤ 2R_{j+1}L^{j+1}.
- Pins: TL 1dafdc3ce602 (labels 70ae4168d982), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 24,080 characters of reviewed blocks, definition check 0 conflicts. The whole part was read. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r5

- No fatal or serious finding. r4's m1, m2′, m3, and m4 are all resolved, and every constant was rechecked and holds. One minor clarity finding (n1), with no mathematical consequence. Not clean.

## Findings and repairs (links_a r5)

- n1 (#629-0-2). The lattice of an "LMR_j-cube" was not stated. The conversion R_jL^j ≤ 2R_{j+1}L^{j+1} holds for CRE (3.16)'s LMR_j-cubes, which are the MR_j-cubes of T_{L^{−j}}, the frame of #629-0-3's cutoff cubes. In T_{L^{−j}}'s own LMR_j-cubes the ratio could be L + 1.
  - #629-0-2 now opens "Here LMR_j-cubes are CRE (3.16)'s, the MR_j-cubes of T_{L^{−j}}."
  - The line is trimmed to 590 characters with no change of content: "(3.16)'s" for repeated CRE citations, "Λ_j less one layer" for Λ_j⁰, and "Λ_jᶜ ⊇ S_j ∪ Ω_jᶜ" for the collar's set.
  - With this convention, Λ_j⁰'s MR_j-cubes of p.259 and D26's ∼-layers are the same cubes, as the reviewer checked.
- Tag diff against r5's snapshot: 629-0-2 only.
- SHAs: TL aedc96066aa2 (labels 8c674c022dd1). PC 47562cd8272f is unchanged.
- Next: links_b r4 (full), then links_a r6 (full).

## Pre-check: pc-links_b-20261107-r4 (full round, prior r3)

- Changed against r3's packet: #755, #795, and #PC4.4. The context lines #629-0-2 and #629-0-2-1 (packet pc-links-a) also changed.
- The whole part (21,244 characters) was read: r3's packet in full this session, and r4's changed passages against it (diff).
- Checks:
  - #755's payers are #725–#726, re-read.
  - #795: 2D_P ≤ 6·2^{d+2}D_P, 21/20 ≤ 6, and 21/10 ≤ 6·½, so #720's terms other than 4MΣℓ_P are at most 6M(σ_g − λ_𝔏Σℓ_P). The links' extent is (3/2)ν_eℓ_P ≤ 4ν_eℓ_P (#629-4). #798's 2 + 9/32 ≤ 5/2 and #799's (9/64)ν_rσ(D) are unchanged.
  - #PC4.4: N_s ≥ 2max(ℓ₁, ℓ₂) ≥ 2 (#749), so a^×_w ≥ 2c_w/M.
- Pins: TL aedc96066aa2 (labels 8c674c022dd1), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 21,244 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_b-20261107-r4

- CLEAN (full round). There is no fatal, serious, or minor finding, and r3's m1, m2, and the #PC4.4 remark are resolved. This is links_b's first clean round; a second full clean round closes it. Three cosmetic remarks change no bound.

## Findings and repairs (links_b r4)

- r1 (#755): *The volume* pays the #π_k(B_P) factor in (6B). In (6C)'s second case, E(Y_i) pays the cubes of a second-class Y_i (#806, re-read). #755 now adds "or by E(Y_i) at the cubes of a second-class Y_i (#806)".
- r2 (#849): the 3ν_r/80 for the small members is per unit of D_P (#857, re-read). #849 now says so and cites #857. The sum is still ≤ (5/2)ν_r per unit.
- r3 (#754): when span(P′) is the whole loop it has no first bond. #754 now says that a slot of P′ lies within 4δ_{P′} bonds behind b: the arc's first bond, or any slot when the arc is the whole loop (4s ≤ 4δ_{P′}, #751).
- These are rewordings of existing sentences; no bound changes and no tag is added. Tag diff against r4's snapshot: 754, 755, 849.
- SHAs: TL 3236b4e3d38b (labels 8c674c022dd1). PC 47562cd8272f is unchanged.
- Next: links_a r6 (full), then links_b r5 (full) for the second clean round.

## Pre-check: pc-links_a-20261107-r6 (full round, prior r5)

- Changed against r5's packet: #629-0-2 only (diff of the packets). Outside it: #754, #755, and #849's rewordings (packet pc-links-b).
- The whole part (24,077 characters) was read: r5's packet in full this session, and the one changed line against it.
- Checks:
  - The convention "LMR_j-cubes are CRE (3.16)'s, the MR_j-cubes of T_{L^{−j}}" agrees with #629-0-3's frame (LM₂R_j-cubes of T_{L^{−j}}, i.e. (3.16)'s L²M₂R_j-cubes) and with #629-0-2-1's R_jL^j ≤ 2R_{j+1}L^{j+1}.
  - Λ_j⁰'s layer is p.259's MR_j-cubes, the same cubes.
  - The shortened clauses change no content.
- Pins: TL 3236b4e3d38b (labels 8c674c022dd1), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 24,077 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r6

- CLEAN (full round). There is no fatal, serious, or minor finding, and r5's n1 is resolved. This is links_a's first clean round; a second full clean round closes it. Two clarity remarks need no correction and were applied as rewordings.

## Findings and repairs (links_a r6)

- Remark (a), #629-0-2: Coll_j's six π_j-layers lie within one LMR_j-layer only for R_j ≥ 6, which the line did not state. R_j ≥ (log g_j^{−2})^r (CRE (2.5), p.255 l.36–39, re-read) gives R_j ≥ 6 for small g_j. #629-0-2 now cites it.
  - The line was trimmed to 600 characters ("S_j = …, R′_j", "X_c's labels being …", "within one LMR_j-layer"), with no change of content.
- Remark (b), "whatever the factor": it means for any factor u ≤ u_𝔏, which #700-1's induction supplies. #570, #700-1, and #831 (packet pc-links-b) now say "whatever its factor u ≤ u_𝔏".
- Tag diff against r6's snapshot: 570, 629-0-2, 700-1, 831. Nothing removed.
- SHAs: TL 59939a2b81ac (labels 8c674c022dd1). PC 47562cd8272f is unchanged.
- Next: links_b r5 (full, the second clean round), then links_a r7 (full, the second clean round).

## Pre-check: pc-links_b-20261107-r5 (full round, prior r4, clean)

- Changed against r4's packet: #754, #755, #831, and #849, all rewordings (diff of the packets). Outside it: #570, #629-0-2, and #700-1 (packet pc-links-a).
- The whole part (21,405 characters) was read: r3's packet in full this session, and the changes of r4 and r5 against it.
- Checks:
  - #754: a whole-loop span has 4s ≤ 4δ_{P′} bonds (#751).
  - #755: #806 pays (5/2)ν_r#π_k(Y_i) per second-class Y_i.
  - #849: 3ν_r/80 per unit of D_P (#857) is at most 3ν_r/80 per unit of the larger count.
  - #831: the factor of an untouched D_g is u_𝔏 (#830), within u ≤ u_𝔏.
- Pins: TL 59939a2b81ac (labels 8c674c022dd1), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 21,405 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_b-20261107-r5

- CLEAN (full round). There is no fatal, serious, or minor finding, and r4's r1–r3 and #831's rewording are confirmed. **links_b is DONE**: r4 and r5 are two consecutive clean rounds, both full. Two cosmetic remarks change no bound.

## Findings and repairs (links_b r5)

- r1 (#844-7): the exponent's C_ϑS^R term uses Σ_kϑ_k ≤ S^R, which holds by #774's definition S^R := Σ(e^{−p₀(g_k)/4} + e^{−31δMR_k/512}) = Σ(ε_k + ϑ_k) (#722, re-read). #844-7 now says "by Σ_kε_k ≤ S^R, Σ_kϑ_k ≤ S^R (#774), and y^R_k = C_yε_k".
- r2 (#806, context): the list of the free decay's uses now includes *Joins*.
- Both are bookkeeping rewordings of existing sentences that state facts already established; no bound changes. pc-rstep r30's range covers them.
- SHAs: TL d9e396233d62 (labels 8c674c022dd1). PC 47562cd8272f is unchanged.
- Next: links_a r7 (full, the second clean round), then pc-rstep r30.

## Pre-check: pc-links_a-20261107-r7 (full round, prior r6, clean)

- Changed against r6's packet: #570, #629-0-2, and #700-1 (diff of the packets), all rewordings of r6's remarks. Outside it: #806, #831, #844-7 (rewordings).
- The whole part (24,107 characters) was read: r5's packet in full this session, and the changes of r6 and r7 against it.
- Checks:
  - R_j ≥ (log g_j^{−2})^r (CRE (2.5), p.255 l.36–39) is ≥ 6 for small g_j, so 6M ≤ MR_j.
  - "whatever its factor u ≤ u_𝔏" is what #700-1's induction supplies.
  - #629-0-2 is 600 characters, with no change of content beyond the citation.
- Pins: TL d9e396233d62 (labels 8c674c022dd1), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 0358d315f174. Size 24,107 characters of reviewed blocks, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r7

Not clean: one minor finding (m1), no fatal or serious finding. Both of r6's remarks are resolved. Every other step is CORRECT, with the arithmetic at d = 4 re-checked. The clean count restarts, so links_a needs r8 and r9 clean, r9 full.

How the pre-check missed m1: it checked #629-2's map citations for content, not for their stated range of steps. #MD2.3.4.46-3 says "for k+1 ≥ 2", and #629-0 allows n(X) = 1.

## Findings and repairs (links_a r7)

- m1 (#629-2, #629-2-1). The network, path and count bounds were cited from map #MD2.3.4.46-1 to #MD2.3.4.46-3, which hold for steps ≥ 2 only, but step-1 links exist (D26 7.4(a), "At n = 1").
- Re-derived from map #MD2.4.12.7, #MD2.4.12.6-3, #MD2.3.5.3-14, #MOMGD.14-4, #MD2.3.4.53-2 to #MD2.3.4.53-3, TL #693 and D2.7 15.4(ii).
  - At step 1 a group's envelope is max-norm connected, holds at most A_E𝔰 π₁-cubes, and contains the group's domain and its hull's cubes. 𝔰 = σ₁.
  - A_E = 9(2R_e + 1)⁴ = 729, independent of L, since R_e = 1.
  - Incompatible groups have touching footprints or overlapping intervals, so their envelopes touch.
  - An R-step has k ≥ 3, so step-1 lengths shrink by L^{k−1} ≥ L²:
    - diameter: 730Mσ₁/L² ≤ 2Mσ₁;
    - halo: LMR₁/4 fine bonds = MR₁L^{1−k}/4 ≤ MR_k/4 step-k bonds, by R₁L ≤ R_kL^k.
  - Cube count: a closed spanning-tree walk of at most 2·729σ₁ cubes, cut into runs of L² consecutive cubes, each run spanning at most L² ≤ L^{k−1} indices per coordinate and so meeting at most 2^d π_k-cubes. That gives 2^d(1458σ₁/L² + 1) ≤ 2^{d+1}σ₁.
- Repair in place:
  - #629-2 and #629-2-1 are restricted to n(X) ≥ 2.
  - New #629-2-2 (step-1 X̂), #629-2-3 (scaling and halo) and #629-2-4 (count). The former closing sentence is #629-2-5, for every n(X).
  - #629-0-1 gives the dependence width as 3M for n ≥ 2 and under MR_k/4 for n = 1.
  - #629-0-3 reads "within 3M of X_c (MR_k/4 at n = 1), so it meets X_c^∼".
  - #629 cites #629-2 and #629-2-2, and #714 cites #629-2-5.
- The envelope symbol is not used, since table #T11.18 has 𝔈_k. A_E is the map's, as TL's #288 and #629-4 already cite it.
- D2.7 l.191 (twice "#629-2-1", once "network joined by paths … #629-2") and l.221 ("#629-2–#629-2-1") were sent to the LF session (owner) with wording.
- Lines: #629-0-1 569, #629-0-3 602, #629-2-2 526, #629-2-3 431, #629-2-4 345 characters. TL is now ca640fa6fa28 (labels e423fe1534d1, 1118 tags).
- Next: links_a r8 (full) after the D2.7 edit, then r9 (full), then pc-rstep r30.

## Pre-check: pc-links_a-20261107-r8 (full round, prior r7)

- Changed against r7's snapshot: #629, #629-0-1, #629-0-3, #629-2, #629-2-1, #629-2-2 to #629-2-5 (new), and #714 (citation). Outside the part: #256 is split at a sentence boundary into #256 and #256-1, because it was 959 characters. Each changed line was re-read in full.
- The whole part was read: r5's packet in full this session, and every change of r6, r7 and r8 against it.
- Citations re-read:
  - map #MD2.4.12.7 (the envelope is connected, has at most A_E𝔰 cubes, and contains X(W) and the hull's cubes);
  - #MD2.4.12.6-3 (σ₁ = 𝔰);
  - #MD2.3.5.3-14 (incompatible groups have touching footprints or overlapping intervals; diameter at most A_dLMΣσ fine bonds);
  - #MOMGD.14-3 to #MOMGD.14-4 (R_e = 1);
  - #MD2.3.4.53-2 to #MD2.3.4.53-3 (ρ_dep < LMR₁/4 fine bonds);
  - TL #693 (k > N_B > N₀ ≥ 1);
  - D2.7 15.4(ii) (R_jL^j ≤ R_kL^k).
- Units: a π₁-cube is LM fine bonds wide and a π_k-cube ML^k, so a π_k-cube is L^{k−1} π₁-cubes wide. A fine bond is L^{−k} step-k bonds.
- Arithmetic:
  - 730/L² ≤ 2;
  - a closed walk through N cubes has 2N − 1 positions and so ⌈(2N − 1)/L²⌉ ≤ 2N/L² + 1 runs;
  - 2^d(2·729σ₁/L² + 1) ≤ 2^{d+1}σ₁ for L² ≥ 1458 and σ₁ ≥ 1;
  - MR₁L^{1−k}/4 ≤ MR_k/4 < MR_k, so a step-1 link reading X_c's labels meets X_c^∼.
- Symbols: A_E is the map's, and #629-2-2 says so, because table #T4.37's A_E is Cauchy's loop constant. The envelope symbol 𝔈 is not used, because of #T11.18. ρ_dep and R_e are not in the table. Definition check: 0 conflicts.
- Consumers: D2.7 l.191 and l.221 now cite #629-2–#629-2-2 and #629-2-5 (LF session, D2.7 971428523236, re-read). TL #629-5 and #720 use only the step-k bounds.
- Size: 25,557 characters with #253–#258, over 25k. Those lines were CORRECT in r6 and r7 and are unchanged apart from the #256 split, so they move to pc-rstep r30 as a block under review. links_a r8 is 22,702 characters. The count had restarted at r7, so the redefined part needs r8 and r9 clean, r9 full.
- Pins: TL 6b85a1325934 (labels 14fb07e80fd8), PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 971428523236. No known weak point. A clean round is expected.
- Queued for r30: add the extract #253–#258 and re-pin.

## Verdict: pc-links_a-20261107-r8

CLEAN (full round): no fatal, serious, or minor finding. m1 is resolved. The reviewer checked that A_E = 729 is independent of L (R_e = 1 for L > 8, #MOMGD.14-3 to #MOMGD.14-4), which r7 had left unverified. This is the redefined part's first clean round.

## Findings and repairs (links_a r8)

- Remark (not a finding), #629-2-3. The line wrote the halo about "its groups' domains and hulls", where the map writes "the network". Reworded in place: "within V3's halo ρ_dep < LMR₁/4 fine bonds of its network, its groups' domains and hulls, inside X̂". The line also cites #MD2.3.4.54-3 to #MD2.3.4.54-4, where the halo is printed. No bound changes.
- TL is now 357edf2f30bf (labels 14fb07e80fd8).

## Pre-check: pc-links_a-20261107-r9 (full round, prior r8, clean)

- Changed against r8's snapshot: #629-2-3 only, re-read in full. #MD2.3.4.54-3 to #MD2.3.4.54-4 were re-read. They print "V3's step-1 dependence set lies in the neighbourhood of the network of radius ρ_dep", and ρ_dep < M(1/2 + C_boxL) < LMR₁/4 for g₀ small.
- The whole part was read: r5's packet in full, and every change of r6 to r9 against it.
- The map ranges in the permitted background now run to #MD2.3.4.54-4, and LFR I runs to p.179 (N > N₀).
- Pins: TL 357edf2f30bf, PC 47562cd8272f, LF e873ea0df345, table d4776667c9bd, D2.7 971428523236. Size 22,755 characters, definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-links_a-20261107-r9

CLEAN (full round): no fatal, serious, or minor finding, and r8's remark is applied. **pc-links_a is DONE** (r8 and r9 clean, both full). With links_b done (r4, r5), both links parts are done.

## Findings and repairs (links_a r9)

- R1 (remark, #629-0-1 and #288). The 3M width for n ≥ 2 covers an old step-1 insertion's halo M(1/2 + C_boxL) fine bonds only if C_box ≲ L, but #288 listed C_box among the constants fixed after L.
  - Re-derived from map #MD2.4.12.6-1, #MD2.4.13.3-2 and #MOMGD.14-4. The map's only conditions on C_box are C_box ≥ 4A_E and C_box ≥ 6, and "the comparison holds for every C_box". A_E = 729 for every L.
  - Repair: #288 now fixes C_box := 4A_E = 2916, independent of L. #629-0-1 is split at its sentence boundary, and #629-0-1-1 states that the step-1 halo is under M step-2 bonds, M(1/(2L²) + C_box/L) < M for L ≥ 2C_box.
  - TL #629-4's C_box ≥ 2916 and D2.7 15.8-1(6-0)'s ν_e ≤ ν/5832 are unchanged.
  - The table entry for C_box was sent to the LF session (owner).
- R2 (remark, #628-1). Reworded: "the blocks' closed continuum cubes of side M". The line went to 626 characters, so its last two sentences are joined, giving 595.
- TL is now ac693d28d0bc (labels 149b0f46ef44). #288, #628-1 and #629-0-1–#629-0-1-1 go into pc-rstep r30 as blocks under review, so that a round sees the changes.

## Verdict: pc-rstep-20261107-r30

Not clean (full round): three minor findings, m1–m3, and no fatal or serious one. r29's S1 is resolved: the q-split agrees with (1.90)–(1.97), the constant 4R_k + 92 is paid by #645 at q ≥ 1, and the constant 4 is paid inside (8α)^{1/3} at q = 0. r29's m-a to m-d are resolved. The totals, the ε̄_A reading, (R-member)'s units (#253–#258), L₀^× and C_box all check. pc-rstep needs r31 and r32 clean, r32 full.

## Findings and repairs (r30)

- m1 (#PC4.14.4-4.5.4, claim (c)). The list of places did not name a single-loop group that (R-member) merges into a cross D_G (#247), and routed its carriers to "member of a single-loop group (#825)".
  - Re-derived: each D_G holds a cross insertion (#247), so it is cross by #PC4.14.4-4.5.1, and the carriers inside it leave the count with it.
  - Repair in place: #PC4.14.4-4.5.4 now reads "lies in a cross group or in a D_G of (R-member) (#761, #799, #247), which leaves the count with it", and the member case reads "a single-loop group g of 15.6 in no D_G". The line would have run to 672 characters, so the continuation is split at a sentence boundary into #PC4.14.4-4.5.4-0.
  - #PC4.14.4-4.5.4-4 reads "Let g, in no D_G, hold a carrier". In #PC4.14.4-4.5.4-7 the productions are "the case-(a) groups in no D_G", which closes the same gap for productions: a case-(a) group with a cross insertion in a slot is linked by #247. The cross sentence is now "R-made groups that meet both loops and the D_G are cross (#766, #844-4, #247)". -7 reached 619 characters, so it is split at a sentence boundary into -7 and -7-0.
  - Claim (c) in r31's spec reads "every single-loop R-made attached content".
- m2 (#812). Reworded in place. The q-parts are named F_q(X′). (1.92)–(1.95) bound each F_q(X′) by the q-term of (1.95)'s right side, and (1.96) sums these terms over q to (1.97)'s bound, so Σ_q|F_q(X′)| obeys (1.97). Re-read against p.388–389: (1.92) applies the triangle inequality to each q-term of (1.91), (1.93)–(1.95) act within each term, and (1.96) is the sum over q. F_q clashes with nothing in TL, PC, LF, D2.7 or the table. The line is 487 characters.
- m3 (permitted background; LF session's files). Table #T4.42's σ̃(c) gave D^∪_P without D2.7 15.8-1(2-2)'s q = 0 constant 4, and LF #5.39-3-1-2 cited 15.8-1(6) and (6-3) without (6-0). Wording for both was sent to the LF session (msg 36284796) and re-derived from D2.7 (2-2), (6-0) and two-loops #645, #814. Waiting for its table and LF SHAs.
- How the pre-check missed them. m1: the places were checked against D2.7 15.5(i) and #825, but not against (R-member)'s merge, whose lines entered this packet in r30. m2: S1's repaired wording was checked part by part, not in the summed form the Kotecký–Preiss sum consumes. m3: after (2-2) changed, the restatements in the table and LF were not grepped. All three checks are added to r31's pre-check.
- PC is now 20c4be5a7c19 (labels 5413632c7300), and TL is a75478526a6f (labels 149b0f46ef44).
- The LF session applied m3 (its message): #T4.42 now carries the q = 0 constant 4, and LF #5.39-3-1-2 cites "15.8-1(6), (6-0), and (6-3)". Both were checked against the files: table d6e4e2dbdcff, LF 81dbed86d9ff, labels 7c7f67d1b2df, and D2.7 971428523236, which is unchanged.

## Pre-check: pc-rstep-20261107-r31 (full round, prior r30)

- Changed against r30's snapshot: #PC4.14.4-4.5.4, #PC4.14.4-4.5.4-0, #PC4.14.4-4.5.4-3-2, #PC4.14.4-4.5.4-3-2-1, #PC4.14.4-4.5.4-4, #PC4.14.4-4.5.4-7, #PC4.14.4-4.5.4-7-0, and TL #812. Each was re-read in full, and the packet diff against r30 shows only these lines.
- m1's sweep: every route of a group in a D_G was checked. The pre-check found that -7-0's wrap sentence and -3-2's D̂_g sentence still covered groups inside a D_G, so both now say "in no D_G". -3-2-1 now reads "A cross group or a D_G with such a domain stays cross". This agrees with D2.7 15.8-1(1-1) ("For a pair, a cross group stays cross"), and a group in a D_G holds a cross insertion, so it is cross by #PC4.14.4-4.5.1. #PC4.14.4-4.5.1-1's "single-loop R-made groups" excludes them by the same line. No other line of PC routes #825 groups.
- m2: #812 was re-read against LFR II p.388–389, (1.91) to (1.97). F_q is new, and it clashes with nothing in TL, PC, LF, D2.7 or the table.
- m3: the restatements of D^∪_P and of (6-0) in the table and the LF were grepped after the change, and they match D2.7 (2-2) and (6-0).
- Citations of the new tags: nothing outside PC cites #PC4.14.4-4.5.4, -4 or -7, and the extract range #PC4.14.4-4.5.4 to -9-1 contains -0 and -7-0.
- All PC lines are ≤ 600 characters. #812 is 487 characters.
- The whole part was read: r30's packet in full before r30, and every change since.
- Pins: PC c2f6d12337a5 (labels c03a98a06570), TL a75478526a6f, LF 81dbed86d9ff, table d6e4e2dbdcff, D2.7 971428523236. Size 23,234 characters, up from r30's 23,009 for m1's named case, definition check 0 conflicts. Claim (c) reads "single-loop". No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r31

Not clean (full round): two minor findings, n1 and n2, and no fatal or serious one. r30's m1, m2 and m3 are resolved, and every other named step is CORRECT. pc-rstep needs r32 and r33 clean, r33 full.

## Findings and repairs (r31)

- n1 (#850, #817, claim (f); context #806, #645). In (6C)'s second case, a domain X′ ⊇ Y_i at its q = 0 part has no first-class component, so #645's payer of the per-domain constants is absent there. Those constants are e^{c_F(4R_k+92)}, which covers D_P's constant in ŷ_g, and #637's e^{2^{d+1}κ}.
  - Re-derived. Every use of D_P sits within e^{c_FD_P}: the weight and the extent by e^{(c_F/2)D_P} (#727), and the reserve and the joins by the rest (#729). So the unpaid part is #645's two factors, at most e^{4R_k + 92 + 2^{d+1}κ} since c_F ≤ 1. A family's polymers are disjoint, so at most one domain contains a given Y_i (#818), and the cost is paid once per Y_i and term.
  - The referee's other option, the constant 4 for D_P at a q = 0 part (15.8-1(2-3-1)), would leave #637's e^{2^{d+1}κ} unpaid. So the cost is booked in E(Y_i) instead.
  - Repair: the new line #806-1 states the cost (#806 would have passed 600 characters). #817 adds 4R_k + 92 + 2^{d+1}κ to E(Y_i)'s exponent and to its second inequality. This is a polylog of order r < p₀ plus a constant, so E(Y_i) ≤ e^{p₀(g_k)/16} holds for small g_k, unchanged. #817 is 594 characters.
  - PC #PC4.14.4-4.5.4-3-1-1 now cites "#806–#806-1, #818".
  - Table #T4.43 restates E(Y_i), so its new exponent, and D2.7 15.8-1(6-2)'s citation "#806–#806-1", were sent to the LF session (msg 48a3c201), together with Q3's cosmetic remark (#T4.42's y_c citation adds (6-0)).
- n2 (#PC4.14.4-4.5.4, wording). A slot-held carrier of a polymer of a cross group, or of a group in a D_G, matched two places with the same outcome. Now reads "else lies in a cross group or in a D_G", so the slot takes precedence.
- How r31's pre-check missed n1. The S1 repair checked the q = 0 constant inside D^∪_P (clusters) but not D_P's per-domain constants for the second-case groups, whose payer #645 needs a first-class component. r32's pre-check checks every use of #645 at a q = 0 part.
- TL is now aa0a50025615 (labels 9bd399683ac7), and PC is dc8444aa57ae (labels c03a98a06570). #806–#806-1 go into r32 as blocks under review.
- The LF session applied the requested edits (its message), and each was checked against the file: #T4.43's E(Y_i) matches #817, D2.7 15.8-1(6-2) cites "(#806–#806-1, #818)", and #T4.42's y_c cites "(15.8-1(6), (6-0), (6-3))". Table efd8b092d938 (labels c35e2c48a27f), D2.7 8ded8be976ff, LF unchanged at 81dbed86d9ff.

## Pre-check: pc-rstep-20261107-r32 (full round, prior r31)

- Changed against r31's snapshot: #PC4.14.4-4.5.4, #PC4.14.4-4.5.4-3-1-1, #806-1 (new), and #817. #806 was not changed, but it enters as a block under review. Each was re-read in full, and the packet diff against r31 shows only these.
- n1: every use of #645 and of "the margin of (1.89)" in TL, PC and D2.7 was grepped.
  - #797 and #835 pay per group, and every group has a first-class component through its slots.
  - #704 and #726 concern the sets X^{(44)}, which exist only around first-class components.
  - #84 is per component, and D2.7 15.8-1(6) l.237 uses (1.89)'s margin for X^{(44)} only.
  - So #645's per-domain constants are the only charge that a q = 0 part leaves unpaid, and #806-1 books them.
  - E(Y_i)'s restatements: #T4.43 (updated by its owner) and D2.7 l.191's "E(Y_i) ≤ e^{p₀(g_k)/16}" (bound unchanged). The bound still holds: 4R_k + 92 + 2^{d+1}κ is a polylog of order r < p₀ plus a constant, inside #817's p₀/32 for small g_k.
  - The cost is paid once per Y_i and term: #818 allows at most one domain containing Y_i, and charging each Y_i ⊆ X′ over-pays a domain that contains several.
- n2: with "else", a slot-held carrier is booked only as ending in its slot. The block case comes before it in the same list, so it takes precedence too.
- Line lengths: #806-1 is 288 characters and #817 is 594, and all PC lines are ≤ 600.
- The whole part was read: r30's packet in full, and every change since.
- Pins: PC dc8444aa57ae (labels c03a98a06570), TL aa0a50025615 (labels 9bd399683ac7), LF 81dbed86d9ff, table efd8b092d938, D2.7 8ded8be976ff. Size 24,164 characters, up from 23,234 for #806–#806-1 under review. Definition check 0 conflicts. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r32

CLEAN (full round): no fatal, serious, or minor finding. r31's n1 and n2 are resolved. This is the part's first clean round, and r33, a full round, would be the second.

## Findings and repairs (r32)

- Cosmetic, D2.7 15.8-1(1-1) (LF session's file). It cites "two-loops #806, #816, #818", where (6-2) cites "#806–#806-1". Sent to the LF session (msg 33a12087) to re-point it. This is bookkeeping and changes no bound.
- Cosmetic, the map. #MOMGD.6's header (l.454) has C_g = 3B₃(2C_box + 6)M, while #MD2.4.4.11 (l.3682) defines C_g := 3B₃(C_box + 6)M from #MD2.4.4.10's M_𝒬 ≤ (C_box + 6)Mℓ_{X(𝒢)}.
  - From #MD2.4.4.6-1, 𝒬 has side ≤ 2R_t + 2M with R_t = C_boxM(t + 1), so half of 𝒬^{∼2}'s side, rounded up to a multiple of R₁M₁, is about C_boxM(t + 1) + 3M + R₁M₁. Which form is right depends on t + 1 against ℓ_{X(𝒢)} and on the rounding.
  - Sent to the LF session (same message) to re-derive and make the two agree. Either form is a constant fixed with C_box and M, so no line of pc-rstep changes: #288 uses only C_box.
- No line of TL or PC changed. Pins unchanged: PC dc8444aa57ae, TL aa0a50025615.
- The LF session applied both remarks (D2.7 741dd3c67d5f, map a53a09865294), and each was checked against the file.
  - D2.7 15.8-1(1-1) cites "(two-loops #806–#806-1, #816, #818)".
  - The map's C_g is now 3B₃(2C_box + 6)M at all four places (l.454, 3680, 3682, 3683). Re-derived: diam_∞X(𝒢) ≤ 2Mℓ (#MD2.4.4.6), so R_t ≤ max(2C_boxM, 2Mℓ + C_boxM) ≤ 2C_boxMℓ for ℓ ≥ 1 and C_box ≥ 2. With R₁M₁ ≤ M, M_𝒬 ≤ R_t + 3M + R₁M₁ ≤ (2C_box + 4)Mℓ. At ℓ = 1, M_𝒬 is about (2C_box + 3)M, so the form (C_box + 6) failed and the factor 2 is needed.
  - TL, PC, and the table never used (C_box + 6).

## Pre-check: pc-rstep-20261107-r33 (full round, prior r32, clean)

- No reviewed line changed since r32: PC dc8444aa57ae and TL aa0a50025615 are r32's pins, so the packet's argument is r32's.
- Background changed only by the two cosmetic remarks above, both checked. #288's C_box claim does not involve C_g.
- The whole part was read: r30's packet in full, and every change through r32.
- Pins: PC dc8444aa57ae, TL aa0a50025615, LF 81dbed86d9ff, table efd8b092d938 (labels c35e2c48a27f), D2.7 741dd3c67d5f, map a53a09865294. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r33

Not clean (full round): two minor presentation findings, m1 and m2, and no fatal or serious one. Neither finding changes a bound, and r32's text was confirmed otherwise. The clean count restarts: pc-rstep needs r34 and r35 clean, r35 full.

## Findings and repairs (r33)

- m1 (PC #PC4.14.4-4, notation). c_𝒢 was the gauged activity in #PC4.14.4-1 to -2.1 ("the rest's value at (1, 0)") but the map's activity in -4, -4.4 and -4.6, and in #PC4.14.2 (c_𝒢 = Y_𝒢(1, 0)).
  - Repair: the gauge lines now write c^n_𝒢. -1 reads "Take c^n_𝒢 := the rest's value at (1, 0), the gauged activity". -1.1 reads Y^d_𝒢 = Y_𝒢 − c^n_𝒢T_𝐔(I(𝒢)), -2 reads "any numbers c^n_𝒢", -2.1 reads "(there c^n_𝒢 = c_𝒢 = Y_𝒢(1, 0))", and -4 reads "the gauged activities c^n_𝒢 of #PC4.14.4-1".
  - c_𝒢 is now the map's activity throughout PC. Its later uses (l.201, 209, 227, 277) concern activities generally and hold for either.
- m2 (TL #849, wording). "|Ψ_g| ≤ O(1)ĉ₁#cubes_k(hull g)" holds only for the clusters without a q = 0 part, since those with one have amplitude α^{1/3} (#812-1). Their part of Ψ(S) is ≤ C_Ψ″ per second-class component, uniformly in S (#815), and lies within E(Y_i) (#818), whose exponent carries C_Ψ″ (#817).
  - Repair in place: #849's parenthetical ends "D2.7 15.6, Ψ_g taking the clusters without a q = 0 part, as those with one are #815's, within E(Y_i), #818". It is 575 characters.
  - D2.7 15.6 (l.183) defines Ψ_g with the same omission, and two-loops #682 and #724 in (6B) use its bound. So the scope belongs at the definition: sent to the LF session (msg d8a67545) to restrict 15.6's two bounds and its split to the clusters without a q = 0 part, and to name the remaining part with #815 and #818.
- Remark (no finding, #814): the referee suggests citing p.377 l.5–6 with (1.67) for C_Ψ″'s uniformity in R_k. Not applied.
  - That argument needs each Y_i^∼ to lie in a component of Z^∼, which was not checked against LFR II here (p.372–388 name Z and the Y_i separately).
  - #814 keeps its citation of D2.7 15.3, which accepts Bałaban's convergence with α^{1/3} at ∪Y_i (pp.389–390). The referee confirmed the uniformity.
- A message to the LF session was sent with wrong SHAs, before the hash output had returned; a correction followed at once (msg aa7fb722).
- TL is now d61e2bc1c18d (labels 9bd399683ac7), and PC is b7f001fd9769 (labels 40e8f8df5352). #PC4.14.4-1 to #PC4.14.4-2.1 are not blocks under review, so r34's pre-check records the rename, and the extract range of r34 adds them if the size allows.
- The LF session applied m2 in D2.7 15.6 (l.183), now D2.7 89c4f98d1645. The clusters with a q = 0 part are split off with C_Ψ″ per component within Π_iE(Y_i) (#815, #818), and the bounds on |Ψ(S)| and |Ψ_g| are stated for the others. It also scoped l.187's Π_ge^{|Ψ_g|} the same way. Both were checked against the file, #812-1, #815 and #818.

## Pre-check: pc-rstep-20261107-r34 (full round, prior r33)

- Changed reviewed lines against r33's snapshot: #PC4.14.4-4 and #849, both re-read in full. The packet diff shows only these.
- Changed context lines: #PC4.14.4-1, #PC4.14.4-1.1, #PC4.14.4-2 and #PC4.14.4-2.1 (the rename to c^n_𝒢), and #261.
  - Adding the gauge lines as blocks would take the packet to about 25.3k characters, over the limit. The rename is bookkeeping, so they stay context and Q1 points the referee at them.
- Every use of c_𝒢 in PC was grepped. #PC4.14.2, -2.1, -4, -4.4, -4.6 and l.201, 209, 227 and 277 now use c_𝒢 as the map's activity or as an activity generally. Only the gauge lines needed c^n_𝒢.
- Every bound on Ψ_g or Ψ in TL and PC was grepped (#36, #37, #261, #680, #682, #722–#724, #824, #849).
  - #682 and #724 bound |Ψ_g|, and Ψ_g is now scoped at its definition (D2.7 15.6).
  - #261 bounds D_G's |Ψ| by Σ_g|Ψ_g|, so it now takes the clusters without a q = 0 part and points to Π_iE(Y_i) for the others. It is 345 characters.
  - The rest name the factor only.
- Size: 24,276 characters, up from 24,164 for #849's clause and -4's citation. Definition check 0 conflicts.
- The whole part was read: r30's packet in full, and every change through r34.
- Pins: PC b7f001fd9769 (labels 40e8f8df5352), TL bf1edec31da8 (labels 1a5ea8a6b62a), LF 81dbed86d9ff, table efd8b092d938, D2.7 89c4f98d1645, map a53a09865294. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r34

Clean (full round): no fatal, serious or minor finding, and r33's m1 and m2 are confirmed resolved. This is the first clean round of the new pair. pc-rstep is done if r35, a full round, is clean too. There are three remarks, r1–r3, which are handled below.

## Findings and repairs (r34)

- r1 (PC #PC4.14.4-4.5.4-8, citation). The clusters of E_k^R holding a polymer with a q = 0 domain take their e^{−p₀} from 15.6(e)'s parenthetical: the first-class component with the slot pays it also where the polymer meets ∪Y_i. #815 alone does not give that reason.
  - Repair in place: "…at the amplitude e^{−p₀(g_k)/2} of *The payment* (#815), which a slot's first-class component gives also where a polymer meets ∪Y_i (15.6(e)), their weights…". This was checked against D2.7 15.6(e).
- r3 (PC #PC4.14.2, context). φ_i's formula used c_𝒢 = Y_𝒢(1, 0), while the large-field terms use c^n_𝒢.
  - Repair in place: "…times Π_{𝒢∈Γ}c_𝒢 (map #MD2.4.13.16); the large-field terms take the gauged activities of #PC4.14.4-1 in place of c_𝒢." It is a pointer, so c^n_𝒢 is not used before #PC4.14.4-1 defines it.
- r2 (TL #814, uniformity of C_Ψ″ in R_k). Not applied: the bound needs no extra decay, for the following reasons.
  - Every cluster counted in #814 contains the whole Y_i (#812-1), so rooting it at one fixed cube of Y_i counts it once.
  - The Kotecký–Preiss constant through one cube depends on d, κ and 15.3's constants only (#T4.43's dependency column). The count of domains through a point in d_k is controlled by κ at fixed β, uniformly in R_k (#T3.34: ½βκ > c_dom and C_X), and (1.97)'s decay is e^{−(1+β)κd_{k,∪Y}}.
  - The R_k-dependent root count is N(Y_i) of #810, and it is already in E(Y_i).
  - The LFR II structure behind the referee's sentence was checked here. Y_i is a second-class component of Z (p.378 l.20–21), and each V(Y) domain meets Z^∼ in whole components of Z^∼ (p.377 l.5–6). So a q = 0 domain X′ ⊇ Y_i contains the component of Z^∼ through Y_i, which gives decay that #814 does not use.
- PC is now f0ec87633f41 (labels 40e8f8df5352, unchanged, as no line moved). TL is unchanged at bf1edec31da8. The LF session was sent the SHAs and r2's reason (msg 11ba82bf).

## Pre-check: pc-rstep-20261107-r35 (full round, prior r34, clean)

- Changed lines against r34's snapshot: #PC4.14.4-4.5.4-8 (under review, 581 characters) and #PC4.14.2 (context, 281 characters). Both were re-read in full.
- #PC4.14.4-4.5.4-8's consumers were checked. P^R_k(Z)'s bound O(1)e^{−p₀(g_k)/2} is unchanged, since 15.6(e) gives e^{−p₀(g_k)} ≤ e^{−p₀(g_k)/2}. "of *The payment*" was grepped in PC and TL, and the other uses (#815, TL l.852, 946, 1005) concern Ψ and need no change.
- #PC4.14.2 points to #PC4.14.4-1's gauged activities without using c^n_𝒢 before its definition, so linear order is kept (the gate's question). The later uses of c_𝒢 (r34's pre-check) are unchanged.
- r2 is not applied, for the reasons recorded above. Q1 asks the referee to confirm them against #810, #T3.34 and #T4.43.
- Size: 24,325 characters, up from 24,276 for -8's clause. Definition check 0 conflicts.
- The whole part was read: r30's packet in full, and every change through r35.
- Pins: PC f0ec87633f41 (labels 40e8f8df5352), TL bf1edec31da8 (labels 1a5ea8a6b62a), LF 81dbed86d9ff, table efd8b092d938, D2.7 89c4f98d1645, map a53a09865294. Packet labels c35e2c48a27f. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r35

Not clean (full round): one minor finding, m1, and no fatal or serious one. r34's r1 and r3 are confirmed applied. The clean count restarts, so pc-rstep needs r36 and r37 clean, r37 full.

## Findings and repairs (r35)

- m1 (TL #814, #T4.43; the uniformity of C_Ψ″ in R_k). At a cube of a second-class Y_i, D2.7 15.3's bound carries the root count N(Y_i), which grows with R_k, while the q = 0 amplitude (8α)^{1/3} is fixed. So "the per-cube constant of 15.3" did not give uniformity.
  - The referee is right, and r34's reasons for not applying r2 (above) were wrong. #T3.34's domain count is for d_k, not for d_{k,∪Y}, in which the cubes of Y_i are free. In E(Y_i), N(Y_i) is a prefactor, while the cluster sum is in an exponent.
  - Re-derivation, read from the transcript:
    - Z is a union of MR_k-cubes (LFR II p.380 l.47–49 at j = k), each a union of π_k-cubes (CRE p.245 l.38–39).
    - Y_i is a component of Z (p.378 l.20–21). So for a π_k-cube r^Y_i off Y_i with a face on Y_i, the MR_k-cube containing it is not in Z and touches Y_i. It is therefore in the layer ∼ adds (CRE p.245 l.41–43), and r^Y_i lies in the component of Z^∼ through Y_i, off Z.
    - A q = 0 domain is the union of its V-domains (p.388 l.14). Those exclude the components of Z^∼ (p.379 l.24–25) and meet Z^∼ in whole components (p.377 l.5–6). So a q = 0 X′ ⊇ Y_i contains r^Y_i.
    - (1.67)'s tree (p.376 l.29–30) meets every π_k-cube of X′∖∪Y. The included Y_j have their r^Y_j there, so they have a face on the tree's cubes. Hence the count is e^{O(1)(n+1)} through r^Y_i, and κ large beats it.
  - Repair in place: #814's last sentence is replaced by the new lines #814-1 (the root, 555 characters), #814-2 (the count, 521) and #814-3 (the rooted sum and C_Ψ″'s dependence, 434). TL is 8734512b0ea7 (labels a79839a1c508), and PC is 1b1e013ee447 (labels 40e8f8df5352).
  - The name r^Y_i was chosen after a clash check: z_j is Bałaban's constant in D2.7 15.3 (l.173).
  - The LF session was asked (msgs aa294139, a176538a) to reword #T4.43, D2.7 15.8-1(6-3) and LF #5.49-1 to the root r^Y_i of #814-1. It applied them as z_i (LF 3f91ff5a81e3, table 5067ff54c4df, D2.7 014433a58127) and was asked for the rename.
- r-a (PC #PC4.14.4-4.5.4-9-1). "C^P(j) is g_* times powers of LR_j" now reads g_*², since e^{−p₀/4} ≤ g².
- r-b (TL #815.2). It now reads "leaves e^{4(2^{d+2}ν_r + (3/4)ν_e)}, < 2 with w^Ψ_c's e^{(3/8)ν_e} per cluster". "The links are paid by #629-4" became "#629-4 pays the links", so the line is 600 characters.
- r-c (PC #PC4.14.4-4.5.4-0). The citation now reads "(#844-2, with #722's bound on η(D) and its status)", a pointer, so the status is stated once, at #722.
- The LF session renamed z_i to r^Y_i in its three lines (LF 724946123ea0, table 08395391f8a2, labels 541357527111, D2.7 6034fd06049a; map unchanged). All three were checked against the files.

## Pre-check: pc-rstep-20261107-r36 (full round, prior r35)

- Changed lines against r35's snapshot, each re-read in full:
  - TL #814 (336 characters), new #814-1 (555), #814-2 (521), #814-3 (434), and #815.2 (600);
  - PC #PC4.14.4-4.5.4-0 and #PC4.14.4-4.5.4-9-1.
- Each citation in #814-1 to #814-3 was re-read in the transcript:
  - LFR II p.378 l.20–21 (Y_i, the second class of components of Z) and p.380 l.47–49 (the cover by MR_j-cubes, a union of components);
  - CRE p.245 l.38–43 (compatible partitions; ∼ adds one layer of the defining cubes);
  - p.388 l.14 (the localisation domain determined by the term), p.377 l.5–6 (Y ∩ Z^∼ a union of components of Z^∼), and p.379 l.24–25 (no V-domain equals a component of Z^∼);
  - p.376 l.26–33 ((1.67), the tree meeting all M-cubes of Y∖Z).
- Uses of C_Ψ″ and #814 were grepped: TL #815, #815.2, #815.2-1, #816-1, #817; D2.7 15.6 l.183 and 15.8-1(6), (6-3); table #T4.42–#T4.43; LF #5.39-3-1-2 and #5.49-1. Only #T4.43, 15.8-1(6-3) and #5.49-1 named the root, and their owner reworded them. The bounds are unchanged.
- New symbol r^Y_i: no other use in TL, PC, LF, the table, D2.7, D2.6 or the map. z_i was avoided, as it clashes with 15.3's z_j.
- Size: the repair took the part to 25,654 characters. #288 and #628-1 were split off into the new part pc-rinputs, which gets its own two clean rounds, and are context here. The part is now 24,512 characters, with definition check 0 conflicts.
- The whole part was read: r30's packet in full, and every change through r36.
- Pins: PC 1b1e013ee447 (labels 40e8f8df5352), TL 8734512b0ea7 (labels a79839a1c508), LF 724946123ea0, table 08395391f8a2, D2.7 6034fd06049a, map a53a09865294. Packet labels 541357527111. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r36

Clean (full round): no fatal, serious or minor finding. r35's m1 is confirmed resolved, and so are r-a, r-b and r-c. This is the first clean round of the new pair, and pc-rstep is done if r37, a full round, is clean too. There are four remarks, R1–R4, which were reworded in place.

## Findings and repairs (r36)

- R1 (#814-1). The step-k fact is stated more directly at p.384 l.24 ("The domain Z is a union of MR_j-cubes"). Reworded to cite "(p.384 l.24, p.380 l.47–49, at j = k)"; the line is 568 characters.
- R2 (#814-2). #T3.34 lists ½βκ > c_dom for counts in d_k, not this count. Reworded: "and (1 + β)κ, net of the c_F uses, above this entropy constant of d (κ large, #T3.34, as p.390 l.4 needs)"; the line is 606 characters.
- R4 (#814-3). The claim holds for the q = 0 parts (X′, 0), which are unions of V-domains. The polymers meeting Y_i without containing it hold a slot.
  - Reworded: "Every q = 0 part (X′, 0) meeting Y_i, a union of V-domains, contains r^Y_i …; the polymers that meet Y_i without containing it hold a slot (#800, #816-1) and enter at Y_i with N(Y_i)e^{−p₀(g_k)/2} ≤ e^{−p₀(g_k)/4}."
  - C_Ψ″ is now "the constant of D2.7 15.3's Kotecký–Preiss bound rooted at the single π_k-cube r^Y_i".
  - The line reached 626 characters, so its second half became #814-4 (332 characters); #814-3 is 308.
- R3 (#815.2 against D2.7 15.8-1(6-3)). Both book the per-cluster e^{(3/8)ν_e} once, but describe it differently. #815.2 is kept, and the LF session was asked to reword 15.8-1(6-3) to match (msg 0e2dc09e). It was also asked to cite #814-2–#814-4 in #T4.43.
- TL is now 14d14c9adab7 (labels 9545e848f247). PC is unchanged at 1b1e013ee447.
- The LF session applied both requests: #T4.43 cites "(#814-2–#814-4)", and 15.8-1(6-3) reads "a cluster's factor e^{(3/8)ν_e} goes with (6-0)'s factor e^{4(2^{d+2}ν_r + (3/4)ν_e)} into the amplitude, < 2 together (two-loops #815.2)". It is table c94afde7eca1 (labels c0928da8b396) and D2.7 2b2692792582, with the LF unchanged. Both were checked against the files.

## Pre-check: pc-rstep-20261107-r37 (full round, prior r36, clean)

- Changed lines against r36's snapshot: TL #814-1, #814-2, #814-3 and the new #814-4 (568, 606, 308 and 332 characters), each re-read in full. PC is unchanged.
- Citations re-read:
  - LFR II p.384 l.24: "The domain Z is a union of MR_j-cubes □", Z there a component of Z_j (l.4–5);
  - #800 (polymers meeting Y_i through a piece, an attached tree, X⁺ or a carried X_D);
  - D2.7 15.3 (a polymer meets C only through a slot). It is cited in place of #816-1, which comes later, so linear order is kept (the gate's question);
  - #811's e^{−p₀/2} multiplicity (as in -4.5.4-9).
- Uses of #814-3 were grepped. Only #T4.43 cited the range, and it now reads #814-2–#814-4. The bounds are unchanged.
- No new symbols.
- Size: 24,811 characters, up from 24,512 for R4's restriction and R2's condition. Definition check 0 conflicts.
- The whole part was read: r30's packet in full, and every change through r37.
- Pins (r37): PC 1b1e013ee447 (labels 40e8f8df5352), TL 0939c25d5443 (labels 9545e848f247), LF 724946123ea0, table c94afde7eca1, D2.7 2b2692792582, map a53a09865294. Packet labels c0928da8b396. No known weak point. A clean round is expected.

## Verdict: pc-rstep-20261107-r37

Clean (full round): no fatal, serious or minor finding, and r36's R1–R4 are confirmed applied. r36 and r37 are consecutive clean rounds, both full, so **pc-rstep is DONE**. There are two remarks, ρ1 and ρ2, which were reworded in place. The reworded lines enter part pc-rinputs as reviewed blocks, so they get two clean rounds of their own.

## Findings and repairs (r37)

- ρ1 (TL #814-3 to #814-4). The slotless q ≥ 1 parts (X′, q) with X′ ⊇ Y_i were not named, and the Kotecký–Preiss weight was not stated.
  - #814-3 adds: "A q ≥ 1 part (X′, q) with X′ ⊇ Y_i contains r^Y_i too, as its first-class components are disjoint from Y_i, and it carries e^{−p₀(g_k)} ((1.95), #812)." It is 463 characters.
    - Check: X′ ⊇ Y_i is covered by V-domains, since the X_{j_h} are first-class components of Z, so #814-1's argument applies. (1.95)'s factor is e^{−q(3/2)p₀} with q ≥ 1.
  - #814-4 adds: "With the Kotecký–Preiss weight ½(#π_k(X′∖∪_jY_j) + #{Y_j ⊆ X′}) on these domains, the criterion's sums through a π_k-cube off ∪_jY_j and at a Y_j are rooted sums of #814-2 and #814-3". It is 511 characters.
    - Check: two overlapping domains share a π_k-cube off ∪Y, or both contain some Y_j (the dichotomy). The weight is at most ½(2d + 1)|S| and is paid by the same decay.
    - The ½ avoids ε, which is the lattice spacing (#T2.3).
- ρ2 (PC #PC4.14.4-4.5.4-7-0). It now reads "with a wrap member and no carrier member", so it no longer overlaps -4's D_g. It is 304 characters.
- TL is 167d0d777b46 (labels 9545e848f247), and PC is b24cc5b7a40a (labels e62a51b5ad52).

## Pre-check: pc-rinputs-20261107-r1 (first round, full)

- The part is new. Its blocks:
  - TL #288 and #628-1, split off from pc-rstep and unchanged;
  - TL #814-1 to #814-4 (#814-3 and #814-4 reworded for r37's ρ1);
  - PC #PC4.14.4-4.5.4-7-0 (reworded for ρ2).
- Each block was read in full. The citations of #814-1 to #814-4 were re-read in the transcript at r36's and r37's pre-checks; the new clauses cite (1.95) (p.389 l.22–25, e^{−q(3/2)p₀}c₀) and #812.
- Uses: #814-3 and #814-4's consumers (#T4.43, D2.7 15.8-1(6-3), LF #5.49-1) cite the range or the root, and need no change. -7-0's only consumer is -7's classification, which the added condition makes exclusive.
- No new symbols. The weight's ½ is a number, and ε was avoided (#T2.3).
- Size: 3,839 characters. Definition check 0 conflicts.
- Pins: PC b24cc5b7a40a (labels e62a51b5ad52), TL 167d0d777b46 (labels 9545e848f247), LF 724946123ea0, table c94afde7eca1, D2.7 2b2692792582, map a53a09865294. Packet labels c0928da8b396. No known weak point. A clean round is expected.

## Verdict: pc-rinputs-20261107-r1

Not clean: one minor finding (m1) and no fatal or serious one. Every block is CORRECT, and #814-3's conclusion holds. Remarks ρ1–ρ4 were repaired too. The clean count of pc-rinputs is 0.

## Findings and repairs (pc-rinputs r1)

- m1 (TL #814-3). The q ≥ 1 reason "as its first-class components are disjoint from Y_i" was incomplete, since X_j's domain is X_j^∼ (p.389 l.9–10). p.387 l.42 prints X_0′ = ∪_{Y∈𝐃}Y ∪ ∪X_j, so the repair covers both readings.
  - Re-derivation: the ∼ layer of X_j consists of cubes that touch X_j and are not in X_j. A Z-cube touching X_j lies in X_j, a component of Z, so the layer is off Z, and X_j ∩ Y_i = ∅. So X′'s V-domains cover Y_i, one of them meets it, and #814-1 gives r^Y_i.
  - New text: "contains r^Y_i too: a Z-cube touching a first-class component X_{j_h} lies in X_{j_h}, so neither X_{j_h} nor X_{j_h}^∼ (p.389 l.9–10) holds a cube of Y_i, a V-domain of X′ meets Y_i, and #814-1 applies; the part carries e^{−p₀(g_k)} ((1.95), #812)". The line is 594 characters.
  - r37's triage check (above) had the same gap, and this repair closes it.
- ρ1 (TL #814-4). Reworded: "X′'s Kotecký–Preiss weight … is ≤ ½(1 + 2d)|S| with #814-2's S, so its exponential joins the entropy constant; the criterion's sum through a π_k-cube c off ∪_jY_j is #814-2's sum with c for r^Y_i, and at a Y_j the sum at r^Y_j of #814-2 and #814-3". "single" was dropped. The line is 596 characters.
  - Check: #π_k(X′∖∪Y) ≤ |S|, since the tree meets every such cube, and #{Y_j ⊆ X′} ≤ 2d|S|. |S| ≤ O(1)(n + 1).
- ρ2 (table #T4.44, the LF session's row). The row says "R_e = 1 for every L", but this holds for L > 11 only (map #MOMGD.14-3). The h_box reading adds no condition beyond C_box ≥ A_E (map #MD2.4.12.7, #MD2.4.12.7-1; V3 L5024 checked). This was sent to the LF session with the re-derivation at 11:16, and #288 now states L > 11 itself.
- ρ3 (PC #PC4.14.4-4.5.1-1). The carrier list included every single-loop R-made group. A group with no carrier member and of species dev or wrap(k) (-7-0, or case (b) by #840) holds no attached content, so it is no carrier in #PC4.14.4-4.5-1's sense.
  - New text: "the single-loop R-made groups of D2.7 15.6 with a carrier member (#825, #839–#843) and the R-step productions (#PC4.14.4-4.5.4-7)". The line is 509 characters.
  - Consumers: #PC4.14.4-4.5-1, -4.5.1-2 (the productions' own root), -4.5.4 and #PC4.14.4-4.12 ("R-step productions included") match. No peer line cites it (grepped).
- ρ4 (TL #288). Now reads "the constants that depend on L, among them κ_s …, M … and κ₁ (½(κ₁ − 1) ≥ 2Lκ, #MD2.4.2.27)", "as R_e = 1 for L > 11 (table #T4.44, #MOMGD.14-3)", and "κ_D′ is non-increasing in L". The line is 508 characters. δ = δ_α/M (#T4.30) is also fixed after L.
- TL is 32a527a92b8e (labels 9545e848f247), and PC is 4999f76e502a (labels e62a51b5ad52). Tags are unchanged.

## Pre-check: pc-rinputs-20261107-r2 (full round, prior r1)

- Every changed line was re-read in the file: #288, #814-3, #814-4 and #PC4.14.4-4.5.1-1. All are ≤ 600 characters (508, 594, 596 and 509).
- The citations were re-read:
  - LFR II p.387 l.40–43, p.388 l.11–14 and p.389 l.9–10, l.22–28;
  - map #MOMGD.14-3, #MOMGD.14-4, #MD2.4.2.27, #MD2.4.12.7, #MD2.4.12.7-1 and #MD2.3.4.54-4;
  - V3 L5022–5028;
  - table #T4.30 and #T4.44.
- Uses: the consumers of the root and of C_Ψ″ (#T4.43, D2.7 15.8-1(6-3), LF #5.49-1) cite by tag, and their claims are unchanged. The carrier list's consumers were checked (ρ3).
- New symbols: none. S is #814-2's, and c is a bound cube.
- #PC4.14.4-4.5.1-1 joins as a reviewed block because its content changed after pc-rstep closed.
- Size: 3,839 → 4,734 characters. The growth is -4.5.1-1 (509) and the repaired reasons. Definition check: 0 conflicts.
- Pins: PC 4999f76e502a, TL 32a527a92b8e, LF 724946123ea0, table c94afde7eca1, D2.7 2b2692792582, map a53a09865294. No known weak point, so a clean round is expected.

## Verdict: pc-rinputs-20261107-r2

Not clean: two minor findings, n1 and n2, and no fatal or serious one. r1's m1 and remarks are confirmed applied. The remarks ρ1–ρ5 were repaired too, except ρ2 (no change needed) and ρ4 (the LF session's row). The clean count stays at 0.

## Findings and repairs (pc-rinputs r2)

- n1 (PC #PC4.14.4-4.5.1-1). "(there is no lw, LF #5.12)" applied LF #5.12 outside its young-pair scope. #PC4.14.4-1 lists lw(Z) among the attached content "at every step".
  - Re-derivation: D2.6 closure 5.0 carries lw(Z) "the same" as att(j, Z), and 7.2 bounds the carried mass of every step-1 species, lw included. So lw(Z) lineages are carriers, with 5.0's weight, paid as D2.6's species in -4.5.4-1 (D26 7.2).
  - New text: "the lineages of att(j, Z), att(j, coll) and lw(Z), which D2.6 closure 5.0 and 7.2 carry alike". -4.5.1-3 now reads "the weight of 5.0 for an att or lw member". The lines are 528 and 362 characters.
- n2 (TL #814-4; table #T4.43). "D2.7 15.3's Kotecký–Preiss bound" and "15.3's constants" misattributed the source.
  - Checked: D2.7 15.3 has the amplitude and the per-MR_k-cube sum O(1)c₁ (l.163–167). 15.4 has the Kotecký–Preiss margin (l.169) and the rooted sums, with O(1)N(Y_i)e^{−p₀/2} ≤ O(1)e^{−p₀/4} at Y_i (l.173).
  - #814-4 now reads "the constant of the Kotecký–Preiss bound for Bałaban's gas (1.90)–(1.97) (D2.7 15.3–15.4) rooted at the π_k-cube r^Y_i". Its weight and criterion moved into the new #814-4-1 and #814-4-2, and the conclusion reads "d, κ, β and α only". The lines are 280, 390 and 245 characters.
  - #T4.43's wording, with the range "#814-2–#814-4-2", was sent to the LF session at 11:40.
  - Bookkeeping, no bound changed: TL #647, #747, #760, #814-3 and PC #PC4.8-5 cite 15.4 in place of 15.3 for the Kotecký–Preiss sums, condition and C_KP. #661 ("15.3's amplitude") and the per-cube sums of #755 are 15.3's and stay.
- ρ5 (#814-4). The slotted polymers' units were implicit. #814-4-1 now gives P the weight ½(#π_k(P∖∪_jY_j) + #{Y_j meeting P}) ≤ ½(1 + 3^d#π_k(P∖∪_jY_j)), with O(1)e^{−p₀(g_k)/4} at a cube and at a Y_j (D2.7 15.3–15.4, κ large).
  - Check: P is connected and distinct Y_j do not touch, so each Y_j that P meets, besides one, touches a cube of P∖∪Y, which touches at most 3^d − 1 blocks. #π_k(P∖∪Y) = O(1)(d_{k,∪Y}(P) + 1) by #814-2's tree, so κ pays e^{a(P)}.
- ρ3 (PC -7-0). It now reads "not of #PC4.14.4-4.5.4-3", as -7 excepts. The line is 286 characters.
- ρ1 (the claim). The spec now reads "off Y_i … lies off Z".
- ρ2. No change: #814-2's |S| = O(1)(n + 1) holds with 2^d or 3^d per piece.
- ρ4 (table #T4.44). This is with the LF session (11:16, accepted 11:2x).
- TL is 9a9a32d09302 (labels 58522b35aaad), and PC is 53f0c51f505b (labels bae1c6792940).

## Pre-check: pc-rinputs-20261107-r3 (full round, prior r2)

- Every changed line was re-read in the file: #814-3, #814-4, #814-4-1, #814-4-2, #647, #747, #760, #PC4.14.4-4.5.1-1, #PC4.14.4-4.5.1-3, #PC4.14.4-4.5.4-7-0 and #PC4.8-5. All are ≤ 600 characters.
- The citations were re-read:
  - D2.7 l.163, 167, 169, 173 and 183;
  - D2.6 closure 5.0 (l.86), 7.1 (l.136) and 7.2 (l.137);
  - pair note #PC4.14.4-1 and #PC4.4-2.
- Uses: only table #T4.43 cites the #814 range, and its rewording was sent. "15.3's" was grepped in TL and PC; the remaining uses cite 15.3's amplitude, sums or decomposition, which are 15.3's. "lw" was grepped in PC (#PC4.14.4-1 and -4.5.1-1 only).
- New symbols: P (a polymer of D2.7 15.3) and the bound 3^d. No clash. Linear order: #814-4-1 and #814-4-2 cite #814-2 and #814-3, both earlier.
- LF moved to 105d808e9cb5 (13a r2's m1–m6, in #4.43-1 to #4.55, with new sub-tags). TL and PC cite none of these tags (grep, 0 hits). Re-pinned.
- Size: 4,734 → 5,949 characters. The growth is ρ5's slotted weight and -4.5.1-2–-4.5.1-3 joining as reviewed blocks. Definition check: 0 conflicts.
- Pins: PC 53f0c51f505b, TL 9a9a32d09302, LF 105d808e9cb5, table c94afde7eca1, D2.7 2b2692792582, map a53a09865294, labels 33a41b23ead3. No known weak point, so a clean round is expected.

## Verdict: pc-rinputs-20261107-r3

Not clean: one serious finding S1, one minor m1, and remarks ρ1–ρ4. Claims (a), (b), (d) and (e) are supported; claim (c) lacked the slotted polymers' decay per π_k-cube. All are repaired below except ρ4, which is the LF session's table row. The clean count stays at 0.

## Findings and repairs (pc-rinputs r3)

- S1 (TL #814-4-1, and #814-4-2 through it). "with it these polymers add O(1)e^{−p₀(g_k)/4} at a π_k-cube and at a Y_j (D2.7 15.3–15.4, κ large)" was unsupported. The slotted weight grew per π_k-cube, while 15.4 gives the groups decay per MR_k-cube only (D2.7 l.169; TL #816).
  - Structural fact used: in D2.7 15.4's gas Ξ^c the slotted polymers enter only as groups, with activity bounded by (ĉ₁)^{#components}e^{−κ(size)} per MR_k-cube (l.169). So the groups' Kotecký–Preiss weight should count MR_k-cubes, and Bałaban's polymers keep their π_k units.
  - Re-derivation. Weights: a(X′) = ½(#π_k(X′∖∪_jY_j) + #{Y_j ⊆ X′}), and a(g) = ν_KPΣ_{P∈g}|P| with ν_KP := ν/2^{d+12}.
    - e^{ν_KP size(P)} is paid by 15.4's Kotecký–Preiss third (l.169).
    - e^{ν_KP|P|_𝔏} is paid by the links. A link meets ≤ 2^{d+2}σ cubes (TL #629-2-5; D2.7 l.191), so it costs ≤ e^{(ν/1024)σ}. That fits in #629-4's quarter: (1/640 + 1/1458 + 1/1024)ν = 0.003225ν < ν/256 = 0.003906ν.
  - Re-derivation. The criterion at a Bałaban unit: the Bałaban polymers give #814-2's sum, ≤ ¼. The groups give their sum through one MR_k-cube, or through Y_j's ≤ 101^d MR_k-cubes (#816), ≤ ¼.
  - Re-derivation. The criterion at a group needs B_Q, the Bałaban polymers meeting an MR_k-cube Q.
    - Q ⊆ Y_l, or Q is off ∪Y, since Z is a union of MR_k-cubes.
    - The polymers holding no Y_j have c₁ = e^{−p₀} ((1.97)) and are rooted at the R_k^d π_k-cubes of Q.
    - A polymer holding Y_l contains r^Y_l. (1.67)'s tree in X′ meets both r^Y_l and Q's cube, so d_{k,∪Y} ≥ mR_k − 1 at distance ≥ mMR_k.
    - At most (2m + 3)^d components Y_l lie in each shell, each with its own MR_k-cube of the box.
    - Half the net rate (≥ 2d for κ large) pays the shells: Σ_m(2m + 3)^de^{−2d(m−1)_+} ≤ 6^d for d ≥ 2. At d = 4 this is 81 + 625 + 0.81 + … ≈ 707 ≤ 1296.
    - So B_Q = 6^dC_Ψ″((8α)^{1/3} + e^{−p₀}) + e^{−p₀/2}.
    - The criterion at g then needs B_Q + 15O(1)ĉ₁ ≤ ν_KP, which holds for α small after d, κ, β and ν and for g_k small.
  - Order of choice: α is small for γ small (LFR II p.377 l.14), and γ is chosen at stage 6 (table #T1.9). ν is fixed by δ_α (#T4.30, stage 2). κ is fixed before the other parameters (CRE p.260 l.27–28, table #T3.34). So the order is admissible, and nothing depends on k or R_k.
  - Text: #814-2 now ends "above twice this entropy constant … their sum at half that net rate is C_Ψ″ times the amplitude", with #814-2-1 "C_Ψ″ is a constant of d, κ and β, and the count is the same through any π_k-cube c off ∪_jY_j".
  - Text: #814-3's slotted clause now reads "so they lie in groups, which #814-4-3 sums at Y_i". It no longer states a separate N(Y_i) term.
  - Text: #814-4 names the gas Ξ^c and gives the bound through the q = 0 parts. #814-4-1 gives the weights, #814-4-2 and #814-4-2-1 the bound B_Q, and #814-4-3 to #814-4-3-2 the criterion and conditions. #629-4-0, split from #629-4, adds the Kotecký–Preiss weight to the quarter's uses.
  - Consumer check. #815, #815.2-1, #817, D2.7 15.6 (l.183) and LF #5.39-3-1-2 need C_Ψ″ per second-class component, uniformly. The repair gives that.
  - Consumer check. D2.7 15.6's bound O(1)ĉ₁#cubes for the clusters without a q = 0 part follows from the same criterion: each such cluster contains a non-q = 0 polymer incompatible with g, and those polymers sum to (15O(1)ĉ₁ + e^{−p₀/2}) per MR_k-cube.
- m1 (PC #PC4.14.4-4.5.1-2; the lw clause of -4.5.1-3). The weight measured ext^{coll} from Coll_{j₁} also for a step-1 root.
  - Checked: D2.6 5.6 (l.98) measures the step-1 extent from 𝒩₁ "in place of ext^{coll}_1", and the O2′ closure §3 (l.44–56, l.97) replaces 𝒩₁ by 𝒩₁′ and gives the bridge dist(Ω_{n+1}, 𝒩₁′) ≥ 5R_{n+1} at every n ≥ 1. 6.4(b)'s ext^𝒩 holds with 𝒩₁′ (O2′ §3).
  - Text: -4.5.1-2 reads "ext^{base} the extent from the root's base: for j₁ ≥ 2 ext^{coll} from Coll_{j₁} …, and for j₁ = 1 ext^𝒩 from the neighbourhood 𝒩₁′ of Λᶜ (O2′ closure §3, superseding 5.6; 6.4(b)'s weights for lw(Z))". -4.5.1-3 gives an att or lw member the weight of -4.5.1-2 "with its extent from its own step's base".
  - Same rule in the consumers. -4.5.2-1's bridge runs from the root's base (O2′ §3 at j₁ = 1). TL #840 (split, #840-1) measures from W₁'s base, Coll_{j₁} or 𝒩₁′, with ext^{base}(D_g) ≤ ext^{base}(W₁) + Δ_g. #843-1 (split from #843), #278 and -4.5.4-5 read ext^{base}(W₁).
  - The letter A was avoided: it clashes with the masses A_j and with U^A and Q^A in PC.
- ρ1 (PC -4.5.4-4). The line now reads "not of #PC4.14.4-4.5.4-3 (so with no localisation domain of a polymer containing a second-class component, #PC4.14.4-4.5.4-3-2)", as -4.5.1-1, -7 and -7-0 except.
- ρ2 (PC -7-0). The line now reads "A single-loop group in no D_G with no carrier member, not of #PC4.14.4-4.5.4-3, is wrap(k) if it has a wrap member, in case (a) (#278, #848) and in case (b) (#842) …; in case (b) without one it is dev, being att only through a non-dev member (#840)". Every non-dev, non-wrap member is a carrier (-4.5.1-1), so such a group has only dev members.
- ρ3 (PC -4.5.1-3). The line now reads "(#737 for wrap(j), j ≥ 2; e^{ν_r𝔰}, #738–#739, for wrap(1))", checked against TL #737–#739.
- ρ4 (table #T4.44, #T4.43). These are with the LF session. #T4.43's dependence becomes "d, κ and β", with the gas Ξ^c and the new condition. Sent with the SHAs.
- TL is cfa587d80cc4 (labels 6dd6db6fdbd3), and PC is 2683261b05c0 (labels 5aacbcfaea65).

## Pre-check: pc-rinputs-20261107-r4 (full round, prior r3)

- Every changed line was re-read in the file: #278, #629-4, #629-4-0, #814-2, #814-2-1, #814-3, #814-4, #814-4-1, #814-4-2, #814-4-2-1, #814-4-3, #814-4-3-1, #814-4-3-2, #840, #840-1, #843, #843-1, #PC4.14.4-4.5.1-2, #PC4.14.4-4.5.1-3, #PC4.14.4-4.5.2-1, #PC4.14.4-4.5.4-4, #PC4.14.4-4.5.4-5 and #PC4.14.4-4.5.4-7-0. All are ≤ 611 characters, and every split is at a sentence boundary. #PC4.14.4-4.5.1-1, #288, #628-1 and #814-1 are unchanged.
- The citations were re-read:
  - D2.7 l.169 (15.4: Ξ^c, the compatibility, the thirds, |P|, hull ≤ 15Σ|P|, c_g := 0) and l.183 (15.6's Ψ(S));
  - D2.7 l.191 (15.8, *The links in the gas*: the a° split, ε, the link's MR_k-cubes);
  - TL #629-2-5, #629-4-1, #737–#739, #816, #818 and #839–#842;
  - LFR II p.389–p.390 l.1 ((1.95)–(1.97), c₁) and p.377 l.14 (α);
  - CRE p.260 l.27–28 (κ);
  - table #T1.9, #T3.34, #T4.30 and #T4.43;
  - D2.6 l.98 (5.6), the O2′ closure l.44–56 and l.97.
- Uses: C_Ψ″ was grepped in TL, PC, LF and D2.7. Every use takes it as a constant per second-class component, and none uses its dependence list except #T4.43, whose rewording was sent. Coll_{j₁} was grepped in TL and PC (#840, -4.5.1-2, -4.5.4-5 only); ext^{coll}(W₁) and ext^{coll}(D_g) were grepped (#278, #843 only). All were fixed.
- New symbols: ν_KP, B_Q and ext^{base} were grepped in TL, PC, D2.7, D2.6 and the table, with 0 hits before. η, B and A were rejected because of clashes (η the lattice spacing and η(D); B the fields and #T4.31's C_B; A the masses).
- Linear order: #814-4-1 to #814-4-3-2 cite #814-2, #814-3, #816 and #818. B_Q (#814-4-2, #814-4-2-1) is stated before the criterion that uses it (#814-4-3-1), and #814-4 and #814-3 cite the criterion forward as the lemma's statement, with no circularity. The gate's first pass had the criterion before B_Q, and the two sub-blocks were swapped before launch.
- LF is 0e208b23ef34. TL and PC cite none of its changed tags (checked at 11:4x). Re-pinned.
- Size: 5,949 → 13,240 characters. The growth is S1's repair, #814-4-3's derivation, and m1's consumers joining as reviewed blocks. Definition check: 0 conflicts.
- Pins: PC 2683261b05c0, TL 3c05b5aa2c61 (labels 71a93c06cf58, after the swap), LF 0e208b23ef34, table c94afde7eca1, D2.7 2b2692792582, labels d60a4e6fd2fb. No known weak point, so a clean round is expected.

## Verdict: pc-rinputs-20261107-r4

Not clean: two minor findings, m1 and m2, and no fatal or serious one. Every block is CORRECT, and r3's S1, m1 and ρ1–ρ3 are confirmed resolved. Remarks ρ1–ρ6 were repaired too, except ρ2 (no change needed) and ρ5 (the LF session's table rows). The clean count stays at 0.

## Findings and repairs (pc-rinputs r4)

- m1 (TL #814-4-3-2). "none of them involving k or R_k" was false. #814-4-2's R_k^dC_Ψ″e^{−p₀(g_k)} ≤ e^{−p₀(g_k)/2} involves R_k, and ĉ₁ involves a_k.
  - Re-derivation: p.389 l.18 prints ¼p₀(g_k) ≥ 1 + 2κ(100R_k)^d, so R_k^d < p₀(g_k), and R_k^dC_Ψ″e^{−p₀} ≤ C_Ψ″p₀e^{−p₀} ≤ e^{−p₀/2} for g_k small. a_k is a polylog of order ≤ r(d + 1) < p₀ (#613), so ĉ₁ ≤ e^{−p₀/2} (D2.7 15.3) is also a condition on g_k.
  - Text: #814-4-2-0 gives the reason "as R_k^d < p₀(g_k) by p.389 l.18". #814-4-3-2 reads "p₀(g_k) large against constants of d, κ, β and ν, that is g_k small: R_k enters the conditions on g_k only through p.389 l.18 (#814-4-2, #814-4-2-3) and through ĉ₁ ≤ e^{−p₀(g_k)/2} (D2.7 15.3), whose a_k is a polylog of order < p₀ (#613), and k not at all".
- m2 (TL #628-1). When an MR_k-cube meets a set was not fixed. The new #628-1-1 reads "An MR_k-cube, a block of the MR_k-partition and a union of π_k-cubes (CRE p.245 l.38–39), meets a set of sites and bonds in the same block sense, so a π_k-cube lies in exactly one MR_k-cube. Diameters, distances, faces, touching and closed-connectedness are those of the blocks' closed continuum cubes". Checked: the uses in #814-4-1 to #814-4-3-1 and D2.7 15.8's link count use this sense.
- ρ6 (D2.7 15.4's group sum through an MR_k-cube, background). The sum was taken as O(1)ĉ₁, but 15.4 l.169 pays only the MR_k-level positions per shape, |P|(2|P| + 1)^d. The M-level shapes and the R_k^d root M-cubes were unpaid. Repaired in TL, and sent to the LF session for D2.7.
  - Shapes, #637-1: (1.67)'s tree of length Md_k meets ≤ 2^d(2d_k + 1) M-cubes (#628-1), which with the fixed domains fix P∖fixed. So the number of shapes is exponential in d_k + 1 at a rate of d, paid by half of #637's free e^{−(β/4)κd_k} for κ large. The other half is (β/8)κ ≥ 3·2^{d−2} ≥ 1 per M-unit, enough for *The free decay*'s c_F ≤ 1 (#636). No other TL line pays polymer shapes (grep "shape", "entropy").
  - Roots, #814-4-2-3–#814-4-2-4: dom P meets one of (2|P| + 1)^d MR_k-cubes Q′, and Q′ lies in at most one first-class component. So the root M-cube is one of the R_k^d in Q′ or of the ≤ 2·3^d(100R_k)^d next to that component.
    - The factor 2: p.389 l.13–14 bounds (1.93)'s (1 + β + β/(3·2^d))κM^{−d}|X_{j_h}| (p.388 l.30) by 2κ(100R_k)^d, so M^{−d}|X_{j_h}| ≤ 2(100R_k)^d. This is derived from that printed estimate, not from LFR I p.177 (i), which p.177 l.23–29 states for the class of components it considers.
    - Each outer M-cube touching X_j touches one of its ≤ M^{−d}|X_j| M-cubes, each with < 3^d neighbours.
    - Total ≤ 3^{d+1}(100R_k)^d ≤ p₀(g_k)/8 for κ ≥ 3^{d+1}, since κ(100R_k)^d ≤ p₀/8 by p.389 l.18.
  - Sum, #814-4-2-5: at most p₀(g_k)O(1)ĉ₁ ≤ e^{−p₀(g_k)/4} for g_k small.
  - Consumers: #814-4-3 now uses 101^de^{−p₀(g_k)/4} ≤ ¼, and #814-4-3-1 uses 15e^{−p₀(g_k)/4}. #849's |Ψ_g| ≤ O(1)ĉ₁#cubes_k(hull g), with its N(Y_i) clause, had the same gap. The new #849-0 derives |Ψ_g| ≤ 2e^{−p₀(g_k)/4}#cubes_k(hull g) from #814-4-3-1's sum at g without B_Q's q = 0 term. Every consumer of #849 (PC -4.5.4-3-1-1, D2.7 15.8-1(6-1) and (6-2), table #T4.42) uses only its rate (5/2)ν_r, which is unchanged. #682's two-loop bound and PC -4.5.4-8 root at π_k-cubes, so no R_k^d count arises there.
- Found in the triage re-read (#814-4-2-0): the tree, taken modulo ∪_jY_j, may cross other Y_j at no cost. So the decay is now taken from the first Y_l that the tree's path from c enters, which lies in X′ (#818), with the path before it off ∪_jY_j.
- The user asked for a proof of the 6^d bound in place of the referee's numerics. The new #814-4-2-2: with t_m := ((2m + 3)/6)e^{−2(m−1)}, t_2 < 1/6 and t_{m+1}/t_m ≤ (9/7)e^{−2} < 1/5. So the sum over 6^d is ≤ 2^{−d} + (5/6)^d + (25/24)6^{−d}, decreasing in d, and (34 + 25/24)/36 < 1 at d = 2.
- ρ1 (TL #278). It now reads "(a polymer of g meets a component, …)" and "Otherwise D_g with a non-dev member continues the lineage …, and one with only dev members is dev (#840)".
- ρ2 (#840 against -4.5.4-4). No change: the two W₁ have different roles, kept apart by -4.5.4-6, and #840-1 holds for any member.
- ρ3 (PC -4.5.1-3). It now reads "from its own root's base".
- ρ4 (PC -4.5.4-4). It now reads "Let a single-loop g".
- ρ5 (table #T4.44, #T4.43). These are with the LF session. #T4.43's range becomes #814-2–#814-4-3-2, sent with this round's SHAs.
- Peer: sent at 12:5x — ρ6's re-derivation (1)–(4), with D2.7's consumers (15.3's Φ bounds, 15.6's O(1)ĉ₁#cubes, c^R_n). From LF: queued behind 13a. The TL derivation (#637-1, #814-4-2-3–#814-4-2-5) makes pc-rinputs independent of that edit, and D2.7 15.4 can cite it.
- Found in the pre-check re-read: #637-1's "fix P∖fixed" now reads "with a choice among the fixed domains having a face on them fix P". #814-4-2-3 reached 697 characters with the factor-2 citation, so its root sentence became #814-4-2-4, and the sum is #814-4-2-5.
- New symbols: t_m (local, 0 prior hits in TL). The name c_sh was rejected (a TL constant) and rephrased without a symbol. #849-1 existed, so the new line is #849-0.
- TL is abbdda1d8519 (labels a53ca44c4ea3), and PC is 0d8714c53735 (labels ff36f9ece8a5). The user paused the next launch (12:5x), so r5 waits for the user's go.

## Pre-check: pc-rinputs-20261107-r5 (full round, prior r4)

- Every changed line was re-read in the file: #278, #628-1, #628-1-1, #637, #637-1, #814-4-2, #814-4-2-0 to #814-4-2-5, #814-4-3, #814-4-3-1, #814-4-3-2, #849, #849-0, #PC4.14.4-4.5.1-3 and #PC4.14.4-4.5.4-4. All are ≤ 600 characters (the longest is 591).
- The citations were re-read:
  - LFR II p.388 l.30 ((1.93)'s factor) and p.389 in full (l.12, l.13–14, l.15–18, (1.95)–(1.97));
  - LFR I p.177 l.20–29 (the class (i)–(ii)), and LFR II p.378 l.1–27 (the two classes);
  - D2.7 item (b) (l.98), 15.3 (l.163–167) and 15.4 (l.169);
  - TL #613 (a_k), #636–#637, #641, #682, #804, #806, #818;
  - PC -4.5.4-8.
- Uses:
  - #637's remaining decay is spent only by *The free decay* (#636), at c_F ≤ 1, and no TL line pays polymer shapes elsewhere (grep "shape", "entropy").
  - #849's consumers (PC -4.5.4-3-1-1, D2.7 15.8-1(6-1) and (6-2), table #T4.42) use only its rate.
  - "O(1)ĉ₁" now occurs in TL only as #814-4-2-5's per-root p₀(g_k)O(1)ĉ₁. PC's ĉ₁ uses cite D2.7 15.3 or 15.6(e), never #849.
  - #628-1's consumers (#629-0-2-1, #629-2-1, #637-1) count π_k-cubes, which is unchanged.
- New symbols: none. t_m was rejected (gate: defined at PC l.219), c_sh was rejected (a TL constant), and #849-1 was taken, so the new line is #849-0.
- Linear order: #637-1 cites #628-1 and #641, both earlier. #814-4-2-3 to #814-4-2-5 cite #637-1, #814-1 and #814-4-1. #814-4-3 to #814-4-3-1 cite #814-4-2-3. #849-0 cites #814-4 and #814-4-3-1, all earlier.
- From LF (13:0x): D2.7 5124e5410d92 repairs ρ6 by citing TL #637-1, #814-4-2–#814-4-2-5 and #849-0, with the factor 2 from p.389 l.13–14. Item 6(b) is unchanged. Hash verified at 13:08.
  - Re-checked what r5 takes from D2.7, all present: item 6(b) (l.98); 15.3's ĉ₁ := e^{3+a_k}e^{−p₀(g_k)} ≤ e^{−p₀(g_k)/2} (l.167); 15.4's |P| layers, (2|P| + 1)^d cubes, chaining, hull ≤ 15Σ|P| and the Kotecký–Preiss third (l.169); and 15.8's "a π_k-cube lies in one MR_k-cube" (l.191).
  - No circularity: TL takes only geometry and the third from 15.4, and 15.4 takes the per-cube sum from TL.
- The peer's point: TL #637 and #651 cited "D2.7 15.3(b)", but the bound is D2.7 item 6(b). Checked: item 6 starts at D2.7 l.88, and (b) at l.98 is the activity bound, Bałaban's variant at p.391 l.15–18 ("the number β is replaced by (1/4)β"). Both lines were re-pointed; #637 also cites p.391 l.15–18. This is bookkeeping and changes no bound.
- Size: 13,240 → 17,324 characters. The growth is the derivation of the groups' per-cube sum, the shell-sum proof, and #637–#637-1 and #849–#849-0 joining as reviewed blocks. Definition check: 0 conflicts.
- Pins: PC 0d8714c53735, TL 1a4cb8d43c18 (labels a98beb26ea25), LF d3c7bb0f430b (labels 7e6166b24c24), table c94afde7eca1, D2.7 5124e5410d92, map a53a09865294.
- No known weak point, so a clean round is expected. The launch waits for the user's go.

## Citation check (user, 2026-11-07 13:31): every Bałaban citation states the print

- Packet citations, repaired in TL (7cbdf14a1778):
  - #814-1-0 now cites p.387 l.42 ("Each term determines the localization domain …") and p.388 l.14.
  - #814-4-2-0 cites c₁ at p.390 l.2, verbatim, and R_k^d < p₀(g_k) from p.389 l.16 at β₀ = 1/7. Line 18 prints the β₀ = 1/7 example as "−(1/4)p₀(g_k)+1+2κ(100R_k)^d≤0".
  - #814-4-2-4 derives M^{−d}|X_j| ≤ 2(100R_k)^d from p.389 l.13–14's estimate at q = 1.
  - #628-1-1 quotes CRE p.264 l.54–55 ("into MR_{k+1}-cubes, is compatible with all the previous partitions") and p.245 l.38–39. It also says that CRE does not define "compatible" and states the set sense used.
- Found by the sweep and repaired:
  - #800-0 and #812-1 put c₁ at p.390 l.2, not l.1, and quote it. #812-1 quotes p.389 l.27–28.
  - #654 and #804 now cite the chain of print: LFR II p.378 l.14–15 and l.21 (the two classes of "the components of Z"), LFR I p.177 l.32–33 (Z is "the union of the above class of components") and l.26 ((i)), and LFR II p.355 l.11.
- Long lines split: #628-1-2, #800-0, #814-1-0 and #814-4-2-0-1.
- Readings in TL: these are not citations. Each must become print, a derivation or OPEN.
  - TL's own: R-chain-start (#86, #156.1), R-chain-norm (#88.1), R-coincides (#157), R-dec-cx and R-small-Z (#17), p.375's inclusion "read as an inclusion of spaces" (#87, #156), (6A) (#503), #617 (15.5(i)), #931 (δ) and #308 (a slip or q₁).
  - Inherited through the map and D2.7 (the LF peer's): R-far″, R-p, R-dec, R-m, R-m′, R-mJ, R-av, R-cpl₀, R-adm, and N read as N_k.
  - R-coincides is refuted as a reading. At n = 0 (h = j), LFR I p.190 (i) and (1.68) give (1 − β(1 − 2^{−(k−m)}))·c·L_0^{2max{0,m−k_0}}, with c = 3 at m = k (p.191 l.13–14). CRE (2.34)–(2.39) at the same layers give (1 − β(1 − 2^{−(k−m)})), so p.191 l.33–34's "coincides" contradicts the formulas, and the n = 0 space is the larger one. TL needs the n = 0 point in CRE's space (the 𝐁-terms' domain, CRE p.261 l.59–60). OPEN until it is derived or rerouted.
  - At n = 0, j = h ≤ k₀, so the L_0 powers and p.190 (ii) drop out (p.191 l.25–27). Only c = 3 on X∩Ω_k differs from CRE. #6.12's margin, ¼β2^{−(k+1−n)}, cannot absorb it. λ ≥ 1 (#48), so the complex parts reach λα_{1,k} > α_{0,k} (RG I p.277 l.54 orders α₀ below α₁), and (2.34) at the final stage does not follow from #92–#123's deviation bounds. The direct route fails.
  - LFR II p.375 l.29–31 ("the space Ũ_k''^c(Y_1,α̃₀,α̃₁) is contained in the analyticity domain of the term 𝐄(X) …") is printed, with its reason at l.33–34. All 15 "read as an inclusion of spaces" now cite it. It covers Bałaban's terms at U_k^0, not TL's chain to U^{(0)}.
  - R-chain-start is OPEN: (1.65) places U_k^0, not U_k″, in Ũ^{(N)c}. R-chain-norm is OPEN: p.191 l.39–42 is printed before the G^c-valued u. R-coincides is OPEN as above. TL #17, #86, #88.1 and #157 say so. (R-eval), and through it D2.7 15.x, rest on these three.
  - R-small-Z is OPEN (#160): p.365 l.35–36 prints only "with some new small terms".
  - Still to check, with their print: R-dec-cx (#17, #130.19), (6A) (#503), #617, #931 and #308, and the inherited R-far″, R-p, R-dec, R-m, R-m′, R-mJ, R-av, R-cpl₀, R-adm, and N read as N_k. These belong to the map and D2.7.
  - Route to close the chain items: work at the un-normalised points, where p.191 l.39–42 is printed. The insertions and the 𝐄- and 𝐑-terms are G^c-invariant (#86), and CRE's 𝐁-terms are invariant when A is transformed too (CRE p.261 l.60–62). Then c = 3 must be handled for the scale-k terms on X∩Ω_k. TL 910ffedb1245 (labels d2c5912e2bcb).
- R-names removed (the user, 13:4x: "they trip mechanical rather than semantic searches"). Each was first checked against its stated derivation:
  - The open items and derived inputs are now cited by tag: (R-eval-old) → #5 (derived, given LF); (R-eval) → #7 (OPEN through #86, #88.1, #157 and #160, as #3 and #7's heading now say); (R-eval-cr) → #220; (R-member) → #241 (PC cites TL #241); (R-round) → #234; (R-att-ext) → #274; R-chain-start → #86; R-chain-norm → #88.1; R-coincides → #157; R-small-Z → #160; R-combined → #206; R-Yi-branch → #819.1.
  - R-dec-cx is RG I p.275 l.6–7's printed claim, quoted at #130.19.
  - The inherited ones are cited by source:
    - R-far″ → D2.7 15.5(ii), with (β) and (α′);
    - R-m′ → q₀ = q₁ > p₀;
    - R-m → CRE p.276 l.11–13 or CRE (2.28);
    - R-mJ → the RMJ closure;
    - R-av → K3's averaging bound;
    - R-dec, R-cpl₀ → map l.928;
    - R-p → map l.928's identification, marked not printed.
  - Bałaban's operation is written 𝐑 (𝐑-step, 𝐑-operation, 𝐑-made, 𝐑-gas, 𝐑-part, 𝐑-terms).
  - #617's "read as" is now a stated definition (a construction choice).
- Still inferred or read in TL, to be derived or made OPEN:
  - #6.16.x: the RMJ closure §7's layers, and the 𝐁_p(X), CRE-cut, 2M₁-unit and own-index items (l.53–l.109, l.314, each "inferred, not printed");
  - #167-2's p₁-or-q₁;
  - N read as N_k (#609, D2.7 item 1(b));
  - #297 and l.556 (V4's step-1 factors, map #MD2.4.5.10);
  - (6A) (#503, l.543, l.1168);
  - S_𝒢 (l.650);
  - #931's δ;
  - the map's l.738 readings (R-dec, R-cpl₀, R-adm) and R-p, which are the peer's.
- TL 9ebd29e5a16a (labels 125c93d68cc4). PC 13fde97f4694 (labels 169f7b602588).

## Recheck of pc-rstep (user, 2026-11-07 13:54)

- Scope: every line of r37's extracts as they now stand. That includes #814-1-0, #814-2-1 and #814-4-1–#814-4-3-2, which were added after r37 and are in pc-rinputs r5's extracts.
- Bałaban pins re-read in the corrected files. All match the print:
  - LFR II p.376 (1.67); p.377 l.5–6 and l.14; p.378 l.14–15, l.20–21 and l.24–31;
  - p.380 l.47–49; p.384 l.24; p.387 l.42; p.388 l.14 and (1.90)–(1.93);
  - p.389 l.9–10, l.12–18, l.27–28 and (1.94)–(1.97); p.390 l.2 and l.4;
  - LFR I p.177 l.26 and l.32–34; CRE p.245 l.41–43; CRE (3.16) (p.268).
- Also checked: D2.7 15.3, 15.4(i), 15.6(d)–(f) and 15.8-1(1)–(6-3); D26 7.4(b)(ii)'s quote; LF #5.39, #5.39-1, #5.39-3-3, #5.40, #5.50 and #5.66-2; table #T1.3, #T1.9, #T3.34 and #T4.43.
- The arithmetic re-done: #814, #814-4-1, #814-4-2-2, #815.2, #817, #254, #257–#258 and #PC4.14.4-4.10–#PC4.14.4-4.13.1.
- Repairs (in place):
  - #814-4-2-0-1 (gap). "The first Y_l that its path from c enters" need not exist: the path to r^Y_j may enter no Y. It now uses that the tree meets r^Y_l of every Y_l ⊆ X′, each within ∞-distance M of Y_l. So d_{k,∪Y}(X′) ≥ dist_∞(c, r^Y_l)/M ≥ mR_k − 1, and X′ is summed at every such root. This is the sum #814-4-2-1 takes.
  - #814-4-2-4 (inference). The bound M^{−d}|X_j| ≤ 2(100R_k)^d was drawn from p.389 l.13–14's estimate. It now uses the printed size, a cube of side 100MR_k (#654), so the count next to the component is 3^d(100R_k)^d. The root count is still ≤ p₀(g_k)/8 for κ ≥ 3^{d+1}.
  - #812-1: the quote now reads ⋃_{i=1}^mY_i, as printed.
  - #815: att(k, Y_i) is cited to 15.6(e)'s scope rule; 15.6(d) gives the insertions.
  - #PC.1-1.2: "𝐑-part of (W)", as LF #5.50 prints it.
  - #PC4.14.4-4.12: M_i is cited to LF #5.40, where it is defined; "read without the drop" became "without the drop".
  - #PC4.14.4-4.5.4-3-1: r(d + 1) < p₀ is cited to #613.
  - #PC4.14.4-4.5.4: "TL #241" became "#241" (#PC.2's convention).
  - ε̄_A: "this note reads LF's ε̄_A as …" is replaced by the symbol ε̄^g_A := 3sup_{j>k−m_W}(ε^{(2)}_A(j) + C^P(j)) + ε^R_A (#PC4.14.4-4.12.1). It bounds LF's ε̄_A, as C^P ≥ 0. It is used in #PC.1-1.2.1, #PC4.14.4-4.13.1, #PC4.14-3a.4 and #PC6.4.1.
  - #PC6.4.1-1 (gap, outside the part). It cited LF #5.66-2, which covers LF's ε̄_A only, for the enlarged value. It now adds C^P(j) ≤ O(1)13^dC_d′(LR_j + 1), a power of log g_j^{−2} by CRE (2.5), hence of log g_k^{−2} + log(k + 1) by LF #5.39-3-3. #PC4.14-3a.4 and #PC6.4.1–#PC6.4.1-1 are in no packet.
- Re-review needed:
  - #814-4-2-0-1 and #814-4-2-4 are in r5's extracts.
  - #812-1, #815 and the PC lines are in closed pc-rstep.
  - pc-rstep reopens for a narrow round on them and their consumers, then a full round. Not launched; it waits for the user's go.
- #814-2 is 617 characters, as at r37's pre-check. The part, with the post-r37 #814-4 block, is 30.2k characters, so a full round needs the split already made (the #814-4 block in pc-rinputs).
- TL 1eb7137f3769 (labels a12bfdf47b7e). PC 441d64a649ad (labels 6842b1613cb4). LF is now 1503106e07dd, so r5's spec needs that hash.

## Readings closed (user, 2026-11-07: "Close all reopened readings! They should all be clear derivations!")

- #157 (n = 0 "coincides"). TL now defines 𝒟^3_k (#6.13). Ũ^{(0)c} ⊂ 𝒟^3_k follows from p.190 (i) and (1.68), with c = 3 on Ω_k; the 3 is absorbed at #6.12.5, #6.14-0 and #130.15.2 (4). Derived, not reviewed.
- #86 (chain start) and #88.1 (normalised stages). These are derived, not reviewed, in TL #86.1–#86.3 and #88.1-1–#88.1-4. They no longer need U_k″ ∈ Ũ^{(N)c}, nor the step after u:
  - #88.1-1: the printed u-free chain from U_k^0 ((1.65)), iterated by p.191 l.39–42, gives W_0 ∈ Ũ^{(0)c} ⊂ 𝒟^3_k.
  - #88.1-2: covariance turns Bałaban's normalised chain into a u-free chain W′ whose sources sit at the rotated variables R(w̄)B_j.
  - #88.1-3: the comparison uses w̄ = e^{Y}v. The printed chain runs at the real variables R(v)B_j, which stay in χ′'s support because Ad_v is an isometry. What remains is a second-order source difference of at most 12c_{nm}c_χδ′_k and a conjugation factor of 1 + c_{nm}L^{−(k−n)}.
  - #88.1-4 (new lemma): differences pass through each step as left factors, with factor 1 + 2c_pδ′_k, so at most 2 over N_k steps.
  - #86.1: B lives on 𝐁₀ ⊂ Λ₀ ⊂ Ω_h. This is derived from CRE (3.2)–(3.5), CRE (2.1) and (2.3), and LFR I p.177 (ii).
  - #86.2: the B-step is W′'s starting difference 𝐇_k″(g_kB), at most Kδ′_k in 𝔹_k″'s weights. Those weights dominate 𝔹_k's (#86.2-1, from (1.10)–(1.12)).
  - #86.3: its share stays below x_i/24 of f_i under the new lower bound q₀ > p₁ + θ_Lν_L, with θ_L = log 2/log L.
  - The slack split is: two conjugations of x/16 each, the B-step x/24 and the σ-part x/48. This gives (1 + 9x/64)(1 + x/16) ≤ 1 + x/4 (#6.13-0, #6.13-1).
- #6.13-1 is tightened from β/8 to β/32. Its "No margin at 𝕌^{(0)} is used" is replaced, because the margin is now shared.
- #88 and #870 said "lies in 𝒟^3_k". They now say 𝒟^{♮,3}_k, since the final stage carries f_n(1 + 9x_n/64).
- #3.2.1.1: the r₀ of LFR II p.363 l.40 is undefined in the print. Its display needs (d−1)ν > 2p₀ + (d−1)r, which ν ≥ 2p₀ + dr gives, so ν_L now uses dr.
- The OPEN marks for #86 and #88.1 are updated at #6, #6.10, #7, #12, #17, #85, #88, #113, #156.1, #158, #213, #870 and #871. #7 is now OPEN through #160 only.
- Lines over ~600 characters were split: #3.2.1.1-0, #3.2.1.1-1, #86-0-1, #86.2-0, #86.3-0, #88.1-0 and #88.1-3-0.
- Table rows used: #T1.2, #T1.4, #T2.23, #T4.4 (CRE's C₀ is not its C₀), #T4.32, #T4.47 and #T4.48. The table has a c_w row (#T4.47), so the new constant is named c_{nm}.
- To the table owner: rows for δ′_j/p₁ (LFR I p.183 l.2), ν_L/N_k (TL #3.2.1.1), θ_L and c_{nm}, and the condition q₀ > p₁ + θ_Lν_L (TL #86.3-2).
- Not yet reviewed. These lines join the next TL packet, with #157.
- TL 278dec6e720c (labels 3c6ac70b32d3).
- Table gap, found while working on #160 (the user, 2026-11-07: "Why are all of these things not in the table???"):
  - The table (d9941a87cd66) has the global determining sets (#T11.16), and nothing else from this machinery.
  - Missing: 𝔹_j(Ω) (CRE p.256–257), the joining (2.14)–(2.15), M_𝐁 with its bond-level Γ₀ (CRE (2.10)–(2.11)), Q_k^{s*} (CRE (1.3)), U_{k,Z} (LFR I (1.74), (1.19)–(1.20)) and χ_{k,Λ} (LFR I (1.75)).
  - Also missing: U_0 as the minimiser of LFR II (1.3) (p.357), the localisation representations LFR II (1.16) and (1.36) and CRE (1.21) with their argument bounds, and TL's U^{post}, 𝐁_k″(Y₁), M and 𝓜.
  - All were announced to the table owner with pins (message of 2026-11-07). TL will cite these rows by tag once the SHA arrives, at d378bceb8701 as #T3.39–#T3.42, #T4.49 and #T11.27–#T11.32.
- CRE's exponent r fixed with r > 1 (the user, 2026-11-07: "If it is a free integer why can't you impose r>1??"):
  - CRE (2.5), p.255 l.36–38, prints r twice. With one value r > 0, L^r ≥ (log g^{−2})^r would mean L ≥ log g^{−2}, false for g small. So the first r is the free integer exponent and the second is Bałaban's parameter, printed nowhere (CRE, LFR I and LFR II grepped; LFR II's r₀).
  - The printed constraints are LFR II p.383 l.28, 2p₁ − (d+5)r₀ > p₀, and p.363 l.40, ν ≥ 2p₀ + dr₀. With LFR I p.198, both hold once p₀ > (d+5)r + 2 + ν is chosen after r. The table's r-dependent rows (#T10.2, #T1.2, #T3.41) are all lower bounds after r.
  - Announced to the table owner as #T1.2 stage 0 and #T2.23 with r = 2 (message of 2026-11-07, table a46455fec8cb); entered by the owner at B1880C2EBB2F.
  - Use: TL #160. With r > 1, e^{−cMR_k} ≤ g_k^n for every n once g is small, against LF #4.48-3.0's dist_sup(Λ, Z^c) ≥ 8MR_k (re-derived from CRE (2.1), (2.3), (3.5) and p.265 l.19).
  - The miss: I wrote that #160 "can't rely on r > 1" without checking the order of choices (#T1.2, #T10.2). The workflow's §2 table grep would have shown r to be a stage-0 choice.
- TL #160, the replacement of U_{k,Z} by U_k (LFR II p.365 l.35–36), derived (2026-11-07 17:05):
  - New file balaban_proofs/BP_LFR2_REPLACEMENT.md, #160.1–#160.8, derived, not reviewed: |δ^{re}| ≤ O(1)(dKM₀ + 1)ε_k per block at a real base on the support. The proof uses VAR Prop 9 and Thm 1, LFR I (1.79) and p.197 l.38–40, LF #3.85.1–#3.86-1, LF #4.48-3.0, (190) and #106, with r = 2.
  - Rows grepped before writing: #T1.2, #T2.23, #T2.24, #T3.27, #T3.29, #T3.34-1, #T4.30, #T4.48, #T11.7, #T11.21, #T11.27 and #T11.29; the ♭ symbols checked against D^♭_m, D^♭_l, K_♭ and ω_♮^♭.
  - The table owner re-derived it (BP 82ACD1C8E48D). The owner flagged log(G^♭u^♭u_0)'s composition. Repaired in #160.8-2: with an Ad-invariant norm, |log x| is the bi-invariant distance, so it is subadditive and no BCH remainder enters.
  - #T4.30's C_mx and δ^{re} clause are changed by the owner (2714EA9F6924), and the R-small-Z reading is gone. The ♭ symbols are #T12.18.
  - TL: #160 is now its statement plus a pointer (#160-1–#160-3), and #45, #161, #165 and l.278 carry O(1)(dKM₀ + 1) in place of O(B₃M₀ + Kd²). #3, #7, #17 and #213 no longer list #160 as OPEN; #7 is derived, not reviewed.
  - labels_two_loops.py now accepts "BP-repl #…" citations. Relabel passes (1182 tags; TL BDE8D2BA86A7).
  - Asked the owner to update D2.7's *Open* list (l.7 and its #7 status line) and the readings inventory's l.12.
- BP_DERIVED_CONFIGS #BC.2 rewritten as definition, claim, lemma and proof; pre-check for bp-crit-bc2-20261107-r1 (2026-11-07 17:59):
  - Why: the user found the old #BC.2 unclear ("is defined only by" hid the identification of p.261 l.10's union). The new text defines 𝐁′, S_X and 𝐁_q(X), cites LFR I p.180 l.49 for ∪ = (2.14), and proves S_X ⊂ Ω_q from (2.14)'s distance hypothesis for both boundary conventions, since none is printed.
  - Print re-read: CRE p.245 l.32–43, p.255 l.1–30, p.256 l.40–63, p.257 l.1–26, p.261 l.1–30; RG I p.251 l.14, p.252 l.22–27, p.262 l.36–60; VAR p.277 l.11–24; LFR I p.179 l.17–24, p.180 l.44–59, p.190 l.8–34.
  - Rows grepped: #T2.15 (M₁ = K_{M′}M′, K ≥ 12d + 1), #T6.19 (∼), #T11.10, #T11.27. New symbols S_X, 𝐁′ checked: no clash in the table, TL or balaban_proofs/.
  - Also changed before launch: #BC.4-1 cites CRE p.257 l.11–12 and p.256 l.49–53 (Bałaban's, accepted) for VAR's theory on 𝐁^X, in place of TL #6.16.3-3-3-0. #BC.2's size: 1 line of 1,060 characters before; 13 lines, 5,627 characters of packet argument after. The banned-word check is clean.
  - Builder: 0 conflicts. The 4 allowed are self-matches of the file under review (Q′, S_X, Ω_{K+1}, Ω_{p+1}). BP e1987bd7533d, LF edbeac67699f, table 9a7f0b531ebe. Medium effort, at the user's request.
  - Known open points in the rest of the file, not in this packet: #BC.5's analyticity of w(V) is not proved; #BC.8 applies the lemma at U_{𝐁_k}(V_k), while TL #6.16 bounds V̂, a complex gauge transform of it.

## Verdict: bp-crit-bc2-20261107-r1

- review.md read in full (2026-11-07 18:22). No fatal findings, 3 serious and 7 minor. Verdict: the claim is correct under the argument's reading of p.261 l.10, but that reading is unsupported as written. Not clean.

## Findings and repairs (bp-crit-bc2 r1)

Each finding re-derived from the print before its repair.
- S1, #BC.2-2: the identification of p.261 l.10's union with (2.14) is presented as printed, and LFR I p.180's union is not "the same union". Accepted.
  - Repair: Bałaban writes ∪ for (2.14) in both orders, global first at LFR I p.180 l.46–51 and localised first at LFR II p.373 l.15–16 (𝐁_k″(Y₁) = 𝐁(Y₁) ∪ 𝐁_k″), as at CRE p.261 l.10.
  - The truncated 𝐁′ is dropped. The proof uses only what the notation gives: every point of 𝐁^X is a point of some Γ_i with i < p, or of a set of depth at most p.
- S2, #BC.2-2-1: the lattice of 𝐁_q(X) is not derived. Accepted, and the re-derivation found a units error that also affects the lemma.
  - RG I p.257 l.2–4 and l.11–12, with LFR I p.179 l.7–8: in T_{L^{−j}}, lengths are in units of j-blocks. So (2.14)'s M₁-cubes for a layer q are M₁L^qη-cubes, and its distance is ≥ 2M₁L^qη, not 2M₁η.
  - For 𝐁_q(X), Ω_n(X) is a union of M₁L^nη-cubes at distance ≥ M₁L^nη from Ω_{n−1}(X)^c, whatever the depth q. The same sites carry the same blocks.
  - The table lacks this convention. I sent the owner a proposed row (18:24).
- S3, #BC.2 and #BC.2-2-2: "block of 𝐁^X" is undefined, and bonds are conflated with blocks. Accepted. The block of a point y of index n is now B^n(y), with points read as in RG I p.251 l.22–24.
- M4, nearest-neighbour convention in #BC.2-3-3/4: accepted. The lemma is reproved with the referee's path argument in ℓ∞ (#T6.1), at cube side M₁L^qη, for inner points, outer points and boundary bonds.
- Remark R (lemma unnecessary): not adopted. It assumes 2M₁η strips. At the correct width 2M₁L^qη, the strip meets Ω_1(X), …, Ω_q(X).
  - What survives is the agreement of 𝐁_q(X) and 𝐁_p(X) on the q-strip for q ≤ p, which reconciles (2.14)'s 𝐁_q(X) with the printed 𝐁_p(X). Proved as a lemma.
- M5, X satisfies (2.14)'s hypotheses without a source: accepted. In the one-layer case they are (2.14)'s stated conditions on its Ω (p.257 l.8–11), and X is that Ω. The several-layer case (l.22–26) needs no distance bound, because its restriction to Ω_q∖Ω_{q+1} places the points in Ω_q.
- M6, "L odd" non sequitur: accepted. Nesting comes from the divisions with corners at L^{−n}Z^d (RG I p.251 l.15).
- M7, sources for blocks of index i and for ∼: accepted. Now VAR p.277 l.21 and CRE p.256 l.62–63 with p.245 l.42–43.
- M8, M₁ ≥ 12d + 1 attributed to K's row: accepted. The bound used is now M₁L^q ≥ 2, from M₁ = KM′ ≥ K (#T2.15).
- M9, compatibility of the partitions: accepted. M₁ = KM′ is a power of L (#T2.5, #T2.15), so the M₁L^qη-cubes belong to the nested divisions of RG I p.251 l.15. No point of T_η lies on a face of one of these cubes.
- M10, implicit Ω₀ = T_η and K for k: accepted. Now written Ω₀ = T_η (Γ₀ = Ω₁^c) and indexed by k.
- Found in the re-derivation: Lemma #BC.2-5 in ℓ∞ points fails in the Euclidean distance for d = 4. In a diagonal configuration the boundary distance is just over 2M₁L^qη.
  - Repaired by using the ML^qη-cubes. X ∈ 𝐃_m and Ω_q are unions of them, and M ≥ L²M₁. Around a common corner z, the boundaries of X and Ω_q have elements within ℓ¹-distance dη.
  - The proof holds for inner points, outer points and bonds, and for the sup, Euclidean and ℓ¹ distances. PRT2 p.223 l.16 uses ℓ¹ for its own paper; CRE prints no metric for (2.14).
  - #BC.1 now states X ∈ 𝐃_m with X ∩ Ω_{m+1} = ∅. Sources: CRE p.261 l.4, and LFR I p.189 l.46 for (1.63)'s domains.

## Pre-check: bp-crit-bc2-20261107-r2 (full round, no prior review)

- 2026-11-07 18:33. #BC.2 is now #BC.2 to #BC.2-6-1, 22 steps:
  - definition and claim;
  - blocks, (C), 𝐁 and (G);
  - cube sizes, the strip and (S);
  - the points of 𝐁^X;
  - lemma #BC.2-4 (𝐁_q(X) = 𝐁_p(X) on S^q_X);
  - lemma #BC.2-5 (S^q_X ⊂ Ω_q);
  - the proof.
- Print re-read for the repair:
  - RG I p.251 l.10–30, p.252 l.19–29, p.257 l.1–16, p.262 l.36–60;
  - CRE p.245 l.20–43, p.254 l.40–60, p.255 l.1–40, p.256 l.18–28 and l.40–63, p.257 l.1–26, p.261 l.1–30;
  - LFR I p.179 l.5–26, p.180 l.40–60, p.189 l.39–46, p.190 l.10–35;
  - LFR II p.373 l.8–22; VAR p.277 l.8–24; PRT2 p.223 l.12–17.
- Rows cited: #T2.5, #T2.15, #T11.27-1, #T11.27-2 (added by the table owner at my request; re-derived by them). New symbols: S^q_X and T^{(n)} as RG I's lattice, with no clash. "Lemma A/B" was avoided, as those names are used in other files.
- Lines ≤ 566 characters. The banned-word check is clean. Builder: 0 conflicts, 4 allowed (self-matches, and LF #3.85's same convention Ω_{k+1} := ∅). BP 106ab6d70a5c, LF edbeac67699f, table cd814aac5ad0, labels 328e517d7d93. Argument 9,677 characters; packet 17,393 bytes. Medium effort.
- The first build stopped on the "prior" field. Its partial directory, which I had created, was removed and rebuilt. The round is full, with no prior review.
- Frozen while the round runs: BP_DERIVED_CONFIGS.md.
- Launched 2026-11-07 18:34 (task b68ypch5g).

## Peer repairs during bp-crit-bc2 r2 (2026-11-07 18:40)

- Source: the LF session's message. I re-derived each item.
  - TL #86.1-1: the upper bound k₀ is false; the range is h ≤ j′ ≤ k. Λ = (Ω^{∼4}_{k₀+1})^c ∩ Z ((1.73), p.192 l.43–44) meets the layers k₀+1, …, k ((1.10), p.179 l.12–17). No step used the bound.
  - TL #87: the n = 0 space lies in 𝒟^3_k (#157-3), not in CRE's Ũ_k^c.
  - D2.7 #7 block: the OPEN labels for #86, #88.1 and #157 are replaced by "derived, not reviewed". The evaluation point is the reduced representative in 𝒟^{λ,3}_k (#6.13, #88).
- New hashes: TL 9499176112b5 (1184 tags), D2.7 5e2af8c989e8. Reported to the peer.

## Verdict: bp-crit-bc2-20261107-r2

- review.md read in full (2026-11-07 18:51). No fatal findings, 1 serious, 9 minor. (C), (G), (S), #BC.2-4, #BC.2-5 (all conventions and metrics) and the unit conversion are confirmed. Not clean. The referee flags a prior-verdict leak: the provenance field summarised r1's counts. Later provenance fields name only the revision.

## Findings and repairs (bp-crit-bc2 r2)

Each finding re-derived from the print (CRE p.245 l.28–46, p.255 l.10–23, p.256 l.45–63, p.257 l.1–26, p.260 l.40–56, p.261 l.1–70; RG I p.251 l.20–28, p.257 l.1–8, p.262 l.36–63, p.263 l.1–15; LFR I p.189 l.35–50, p.190 l.1–32).
- S1, #BC.2-3-2: the q-strip for the points of 𝐁_p(X) at a layer q < p, and the domain Ω_p, are presented as following "by (2.14)". Accepted as written; the q-strip is derived, not read:
  - In (2.14) one index j names the layer containing ∂Ω, the depth of 𝐁_j(Ω) and the cubes of ∼, the M₁-cubes of T_ξ with ξ = L^{−j} (p.257 l.8–11 with p.256 l.57–63). l.22–26 forms, on each domain, "the corresponding determining sets restricted to the domains".
  - So on a domain Ω_q∖Ω_{q+1}, q < p, of the global set {Γ_i}_{i<p}, the strip is S^q_X and the localised set is 𝐁_q(X). By #BC.2-4 its points in S^q_X are those of 𝐁_p(X), so p.261's name 𝐁_p(X) gives the same set. Under ∼ for M₁L^pη-cubes the formula is not (2.14) at that domain, as its cube index differs from the layer of ∂X.
  - The Γ_i, i < p, cover Ω_p^c; on X ∩ Ω_p the only set named is 𝐁_p(X). The proof uses there only that no set entering has a point of index above p, which the referee confirms holds under any reading.
  - "Layer domains … and Ω_p" is now stated as this partition, with no added global layer.
- M2, q ≤ m for the layer met by ∂X (outer or bond convention): accepted. Derived: in the one-domain case an element of ∂X in Ω_{m+1} gives an element of ∂Ω_q ∩ X within distance η, against (2.14)'s hypothesis; in the several-domain case the points lie in X ∩ (Ω_q∖Ω_{q+1}).
- M3, "CRE p.261 l.4, with m = j": accepted. The hypothesis X ⊂ Ω_{m+1}^c, X ∈ 𝔻_m is LFR I p.189 l.46, for (1.63)'s domains, which are the domains of LFR I p.190 l.13–15's spaces used by the two-loops note. #BC.1 now cites only that.
- M4, range of p: accepted. LFR I p.190 l.31, p = 1, …, k.
- M5, X^{∼−2} undefined and "touch": accepted. X^{∼−2} := (X^{∼−1})^{∼−1}; touching cubes are distinct cubes of the division with a common point (p.245 l.41's "touching").
- M6, "layer of index n" of a joined set: accepted. A point of 𝐁^X has the index of its layer in the set it comes from; the index is unique (#BC.2-1).
- M7, alignment of cube families and "faces only": accepted. RG I p.257 l.3–4 (closed M-cubes centred in T^{(j+m)}) and CRE p.245 l.38–40 (compatible partitions); (C) now says A's cubes other than Δ′ meet Δ′ in faces.
- M8, the letter m: accepted. (C) uses l, (G) uses h, and #BC.2-1-2 no longer writes the exponents of M, M₂.
- M9, LFR II's ∪: accepted. It is cited for the order only.
- M10, RG I p.251 l.25–28 and "closed": accepted. RG I p.257 l.3 prints closed cubes for π_j.

## Pre-check: bp-crit-bc2-20261107-r3 (full round, no prior review)

- 2026-11-07, after the r2 repairs. #BC.2 to #BC.2-6-1, 26 steps. New steps: #BC.2-1-3 (cube families), #BC.2-2-1 (the strip), #BC.2-3-2 (one index in (2.14)), #BC.2-3-5 (q ≤ m). Renumbered: (G) #BC.2-1-4, (S) #BC.2-2-2, #BC.2-3-3/-4; references inside the file updated, none outside it.
- Print re-read: as listed under the r2 findings, plus CRE p.255 l.19–21.
- Rows cited: #T2.5, #T2.15, #T11.27-1, #T11.27-2. No new symbols beyond X^{∼−2} := (X^{∼−1})^{∼−1}. Letters: (C) l, (G) h, the corner path P₀, …, P_t.
- Lines ≤ 580 characters; banned-word check clean; tags unique, no dangling references. Builder: 0 conflicts, 6 allowed (self-matches and LF #3.85's Ω_{k+1} := ∅). BC 6b6823432600, LF 0e0a28f49094 (the peer's current file), table cd814aac5ad0, labels 48aa1d1831b3. Argument 11,455 characters; packet 19,194 bytes. Medium effort. Provenance names only the revision.
- Frozen while the round runs: BP_DERIVED_CONFIGS.md.
- Launched 2026-11-07 18:57 (task b4e46s4bz).

## Verdict: bp-crit-bc2-20261107-r3

- review.md read in full. No fatal findings, 1 serious, 6 minor. Not clean. The claim is confirmed apart from S1.

## Findings and repairs (bp-crit-bc2 r3)

- S1, p.261's ∪ read as (2.14) at each layer's index q: repaired. (2.14) prints 𝐁_j(Ω) at the index j of the layer containing ∂Ω (CRE p.257 l.8–11, p.256 l.58), and lemma #BC.2-4 shows that 𝐁_p(X) and 𝐁_q(X) have the same points in S^q_X, so p.261's 𝐁_p(X) gives the same set. #BC.2-3 cites LFR II p.373 l.26–27.
- M1: #BC.2-4 states q ≤ min{p, m}, and #BC.2-4-1 builds 𝐁_p(X) as the maximal sequence for every p ≤ k.
- M2: citations corrected; the RG I p.262 citation in #BC.2-4-1 was removed.
- M3: "touching" is defined in #BC.2-2-1.
- M4: #BC.2-3-1 and #BC.2-3-1-1 cover the domains Ω_i∖Ω_{i+1}, i < p, and Ω_p.
- M5: the Ω_{p+1}(X) := ∅ convention was removed, and the index sets are defined in #BC.2-2.
- M6: #BC.1-4 defines 𝐁 by (2.2) as printed.
- Later repairs (user, 7 Nov): meta sentences removed, the layer defined by (2.2), unsupported VAR p.277 citations replaced by derivations, and #BC.2-3-1 split at #BC.2-3-1-1.

## BC.3–BC.8 rewrite (2026-11-07, before bp-crit-bc38 r1)

- #BC.3-1: VAR (1) for 𝐁^X now has VAR's R, M₁ = R′, M′ (#T2.15, #T2.5), so RM₁ ≥ 2dL. Before, it wrongly used CRE's M₁ ≥ 12d + 1. Its consumers #BC.4-2, #BC.4-4-1 and #BC.5-1-3 were updated.
- #BC.5 is rebuilt on the Landau representative G(V) := e^{iη𝓗(B)}U₀ (VAR Proposition 9, (19)), the two-loops note's V̂, with 𝒱 a ball of radius ρ independent of g (#BC.5-1-4):
  - the Schwarz bound t(B) ≤ (2B₅/C₁)|B| (#BC.5-1-2);
  - the data of 𝐁^X within 2Lt(B), by CMP98 (131) (#BC.5-1-3);
  - the real case via the exact covariance of the averages (CMP98 p.027 l.2) (#BC.5-2-1).
- #BC.7 is written at the spacing η, with J's scaling (s/η)³ stated (#BC.7-2). CRE's ξ is now used only for CRE's own rooms. π is the Hilbert–Schmidt orthogonal projection (inferred, not printed: RG I p.261 l.40 prints "the projection").
- #BC.8, which was OPEN, is now a proposition with proof: Θ ≤ (1 − δ)^{−4}e^{d(t+t^X)}. The proof uses the path inside a block of 𝐁^X, w = 1 at its centre, and REG (1.70)–(1.72) for the Landau transformation of F. In #BC.8-5, sup Θ = 1 + O(r^{ext}_k).
- Pins checked: REG p.076 l.31–47, l.41; p.077 l.47–51; p.078 l.44–48; p.079 l.11–13; p.088 l.36–60; p.089 l.35 (file − 1). VAR p.277 l.11–23; p.278 l.15, l.39–44; p.280 l.45; p.281 l.1–10; p.305 l.30–44; p.307 l.4–5; p.309 l.8–16. CMP98 p.020 l.17, l.25–30; p.026 l.15, l.46–52; p.027 l.2; p.034 l.2; p.036 l.49–52; p.037 l.2–49; p.038 l.1–15. RG I p.261 l.36–40; p.262 l.41–55. LFR I p.190 l.12–18. CRE p.257 l.1–20; p.261 l.4–24.

## Pre-check: bp-crit-bc38-20261107-r1 (full round, no prior review)

- 2026-11-07, BC 3330ea6a4768. Under review: #BC.3 to #BC.8-5, 44 steps, 18.3k characters. Context: #BC.1 and #BC.2 (2.3k and 9.0k).
- Every changed line was re-read. Uses of RM₁, Ω^X_j, Λ^X_j, G(V), F(V), 𝒱, t, t^X and Θ were grepped and agree.
- Renamed against table clashes: f_n → f_{m,n}, as #T4.47's f_n has k in place of m; δ → δ_F, as #T4.30's δ is unrelated. Rows cited: #T2.5, #T2.15, #T4.47, #T11.10, #T11.27-1, #T11.35.
- Each cited display was quoted against the print (pins listed above).
- Directions checked:
  - (1 − δ_F)^{−1} ≥ 1 + δ_F;
  - |log(1 + Z)| ≤ 2|Z| for |Z| ≤ ½;
  - (s/η)³ for J;
  - the path has at most d(L^n − 1)/2 bonds.
- Labelled reading: π as the Hilbert–Schmidt orthogonal projection (#BC.7); none other known.
- Lines ≤ 622 characters. Banned words clean; tags unique; no dangling references.
- Builder: 0 conflicts, 28 allowed (self-matches and other notes' local letters). LF 390958a9ef1a (the peer's current file), table 87b4d88d2560, labels 5eaa220c2f08. Argument 29,846 characters with context; packet 40,031 bytes. Medium effort.
- Frozen while the round runs: BP_DERIVED_CONFIGS.md.
- Launched 2026-11-07 20:09 (task btxyic53r).

## The two-loops note's derived configurations point to BC

- 2026-11-07 20:15, two-loops note 5544736d6a31, labels regenerated (1153 tags, no missing references).
- #6.16.3-2 and #6.16.3-2-1 now state U^d = 𝐔^w and the conjugated curvature and current. They cite BP_DERIVED_CONFIGS.md #BC.5–#BC.8 for (2.35) and (2.37) from (2.34) and (2.36), with the rooms divided by sup Θ. The old #6.16.3-2-1 to #6.16.3-6-1 (the cut domains X_x, N^b, q^d, C^d, a*) are deleted, as BC supersedes them.
- #6.16.4-2 and #6.16.4-2-1 were rewritten. V̂ takes at most s^U_n + ½ of (2.34)'s and (2.36)'s rooms; f_n ≤ f_{m,n} for m ≤ k; the derived configurations take at most sup Θ·(s^U_n + ½), which is < ⅔ for g small. Consumer check: #6.16.5 needs more than a third of each room left, and #6.16.4-2-1 gives that.
- The "(2.37) at the own index" reading was removed from #6.14-1, #6.16.5 and #167-8. #6.14-1 now cites #6.16.3-2-1, with the complex part O(λ_wα_{1,k}) per datum (#16, #52.1).
- c_ext := (1+β₀)/(2LK); #167-1-1 (C_mJ) is deleted. Consumer check: #167-5 and #6.16.4 need 2Kr^{ext}_k ≤ ((1+β₀)/L)α_{0,k}, which still holds. #BC.8-5 needs r^{ext}_k → 0, which also holds. D2.7 15.7 needs g_k·polylog, which still holds.
- Messages sent:
  - to "yang mills 4 handover (2)": the RMJ note §4–§7 is no longer used, and c_ext is larger (D2.7 consumes r^{ext}_k);
  - to the table fork: #T4.50 drops C_mJ; #T12.2 drops s^U_0, s^X, ε^D and X_x; a BC row is offered.
- Table fork: rows updated, table now 26584851201e (checked). #T4.50 has c_ext := (1+β₀)/(2LK) with source #167-1; #T12.2 no longer has s^U_0, s^X, ε^D or X_x; no row cites C_mJ or #6.16.3-3. New #T12.27 records BC's Θ(x), f_{m,n}, t, t^X and δ_F. The next BC build must carry the table's new SHA, and must either add allow_defs for #T12.27's entries (the row records BC's own definitions) or cite the row.
- Peer reply, 20:18: D2.7 is unchanged. It uses r^{ext}_k only as the Cauchy radius (15.6(d), 15.7), so a larger radius lowers its bounds, given #167-5's analyticity. 1/c_ext is still fixed after L and M, and D2.7 never named C_mJ.

## Verdict: bp-crit-bc38-20261107-r1 (0 fatal, 2 serious, 13 minor)

- Completed 20:23. Review read in full. The referee disclosed context exposure: AGENTS.md was injected, but it says nothing about BC.
- S1. #BC.5-1-3-1 took the log of the relative average for CMP98's Q_n. By CMP98 (92) and (97), the relative average is v_n(c₋)e^{iQ_n}R(Ū₀ⁿ)v_n(c₊)^{−1}. The table already had this, at #T6.5, and I did not grep it before writing (workflow §2). It reaches #BC.5-1-4, #BC.8 and #BC.8-1.
- S2. #BC.8-2 applied REG (1.70)–(1.72) at complex data without a derivation: REG's inequalities use unitarity, and REG also uses CMP98 (105)–(106).
- Minor findings:
  - M1: #BC.8-5, g-independence of ε₁.
  - M2: #BC.4-4, the scope of (∂W)(p′) and why W̄ = Ū^j.
  - M3: #BC.4-5-2, the meaning of "critical".
  - M4: #BC.4-4-1, M₁ overloaded and "power of L" missing.
  - M5: #BC.4-3, "plaquette of X".
  - M6: w on X against X̂.
  - M7: strict against non-strict inequalities.
  - M8: localisation of (131).
  - M9: 𝓗(0) = 0.
  - M10: #BC.7-2, 𝐉 = J(𝐔).
  - M11: #BC.3-1, the disjointness citation.
  - M12: #BC.6, REG p.076 print line 40.
  - M13: #BC.8, the hypotheses for (1.71) are not listed.
- Further points to tidy: #BC.3-1, VAR (1) for 𝐁^X (quote CRE p.257 and VAR p.277 l.10–16); #BC.4-2, Ω^X_j ⊂ Ω_j in one line; #BC.4-6, minimiser ⇒ critical; #BC.5-2-1, U_𝐁(V) as the axial representative; #BC.5-3-1, drop the redundant normalisation; #BC.3-2, cite CMP98 p.024 l.9.
- The π label (Q6) was judged accurate. It is replaced by the derivation queued below.

## Repairs (bc38 r1)

- S1 is repaired in #BC.5-1-3–#BC.5-1-3-4 (the lemma |B^X| ≤ C_{BX}Lt(B), C_{BX} := 32d + 8, under Lt(B) < ½c₃ and (8d + 2)Lt(B) ≤ ¼), and S2 in #BC.8-2–#BC.8-2-2 (|v − 1| ≤ e^{5dt^X} − 1 ≤ 10dt^X =: δ_F, with t^X := (2B₅/C₁)C_{BX}Lt).
  - Each point factor (105) is the exponential of a block average of logarithms of contour products of at most d(L − 1)/2 R̄-conjugated e^{iQ_j}. R̄ is conjugation by a unitary, so norms are kept.
  - The elementary bounds are |Πa_i − 1| ≤ e^{Σ|a_i−1|} − 1, |e^Y − 1| ≤ e^{|Y|} − 1, |log Z| ≤ 2|Z − 1| for |Z − 1| ≤ ½, and |Q_j| ≤ 2Lt(B)L^{j−n} (respectively 2t^XL^{l−n}) by CMP98 (131), at the point's own level n.
  - v is CMP98 (106) at the Landau field. This holds at real B by the uniqueness at CMP98 p.031 l.20 (REG p.088 l.37–38), and on 𝒱 by the identity theorem.
- Minor findings: M1 in #BC.8-5; M2 in #BC.4-4, #BC.4-4-1; M3 in #BC.4-5-2; M4 in #BC.4-4-2; M5 in #BC.4-3; M6 in #BC.4, #BC.4-6; M7 in #BC.8-1, #BC.8-3; M8 in #BC.5-1-3-1-1; M9 in #BC.5-1-1; M10 in #BC.7-2, #BC.8-5; M11 in #BC.3-1-1; M12 in #BC.6; M13 in #BC.8 (hypotheses t^X < ½c₃, δ_F < 1). The further points are in #BC.3-1-1, #BC.4-2, #BC.4-5-2, #BC.5-2-1, #BC.5-3-1, #BC.3-2.
- #BC.7, π: the derivation queued below was not tight (the action's linear term pairs (1 − π)Im ∂U₀ only through D*A, so it forces D*(1 − π)Im ∂U₀ = 0, not orthogonality). RG I prints "the projection" onto 𝔤^c and names no complement (p.261 l.36–41), so #BC.7 now defines π as the orthogonal projection for tr X*Y and says what RG I prints. This is a definition, which #BC.7-1 uses through πR(w) = R(w)π.
- Lines over ~700 characters split at sentences: #BC.2-3-3-1, #BC.3-1-1, #BC.4-4-1 (old #BC.4-4-1 is now #BC.4-4-2, cited nowhere), #BC.5-1-3-1-1; citations of VAR (1) and of block disjointness re-pointed to #BC.3-1-1.
- C_d renamed C_{BX} (bookkeeping): C_d is #T12.9's C_β(γ_d) and the random-walk constant of #T11 rows; C_{BX} occurs nowhere else.
- Repaired BC sha 59a87ac1e28a (33,794 characters; r1 snapshot 36,327 bytes).
- Pins (corrected file = print): CMP98 (92) p.031 l.55–59; (97) p.032 l.28–35; (99) p.032 l.49–53; (105)–(106) p.033 l.37–46; uniqueness p.031 l.20; Proposition 3 p.036 l.49–52; (127) p.037 l.2–8; (130)–(131) p.038 l.1–15; α₁ ≤ ½c₃ at p.038 l.17. The table rows #T6.5-1 and #T6.5-2 are pending: the table is frozen and the rows are held in WILSON_IT1_TABLE_PENDING_ROWS_2026_11_07.md.

## Queued for BC after bc38 r1 (BC frozen)

- All applied (see Repairs): #BC.4's minimal orbit, #BC.8-5's tags, and #BC.7's π (as a definition; the derivation once queued here was not tight).

## Pre-check: bp-crit-bc38-20261107-r2 (full round of #BC.3–#BC.8-5)

- Files: BC 59a87ac1e28a, LF 49628896d858, table c6beb03f3952, TL 5544736d6a31. The part under review is 21,939 characters (≤ 25k), with #BC.1–#BC.2 (11,864) as context.
- Changed lines re-read in full: #BC.3-1, #BC.3-1-1, #BC.3-2, #BC.3-4-1, #BC.4 through #BC.4-6, #BC.5-1-1, #BC.5-1-3 through #BC.5-1-4, #BC.5-2, #BC.5-2-1, #BC.5-3-1, #BC.6, #BC.7, #BC.7-2, and #BC.8 through #BC.8-5. #BC.2-3-3-1 was split off only.
- Symbols grepped across BC, TL and the table:
  - t^X, δ_F and C_{BX}: every use is consistent with #BC.8 and #BC.5-1-3. The TL's #6.16.3-2-1 cites the bound (1 − δ_F)^{−4}e^{d(t+t^X)}, which is unchanged.
  - #T12.27 still has the old t^X and δ_F. The fork has confirmed the new values, and they are held in the pending-rows file. The spec marks #T12.27 superseded.
  - C_d clashed with #T12.9 and was renamed C_{BX}.
  - #BC.3-1 citations: those for VAR (1) and block disjointness now point to #BC.3-1-1.
  - No dangling #BC tags and no duplicate tags. No banned words.
  - All lines are ≤ 643 characters, with LF endings throughout.
- Cited displays re-read against the transcripts:
  - CMP98: (56) p.027 l.11; (69) p.029 l.29–31; (97) p.032 l.28–35; (105)–(106) p.033 l.37–46; uniqueness p.031 l.20.
  - REG p.088 l.37–38 (u₁ is given by (106)) and RG I p.261 l.36–41 ("the projection").
  - Units in #BC.8-2-1: |η𝓗^X| ≤ t^XL^{−n} per bond, so |A′| ≤ t^X at L^nη = 1. F₀'s curvature on Ω^X_n is < B₃ε₁^XL^{−2n} = B₃ε₁^Xη′².
  - Inequality directions in #BC.8-2-2: σ_l < dt^X < 1/10 ≤ ¼, and e^{5dt^X} − 1 ≤ 10dt^X for 5dt^X ≤ ½.
- Known weak points: none. π is a definition with the print stated. The identification of v with (106) rests on CMP98's printed uniqueness and REG's use of it in the general sequence of domains.
- Spec specs/spec_bc38_r2.json; definition check: 0 conflicts (37 allowed). Launched 20:48 as task bxdcvuf38 (medium effort).
## Queued for BC and TL during bc38 r2 (BC frozen)

- Scope of #BC.6 and #BC.7, found by the consumer check of TL #6.16.3-2. CRE (2.35) and (2.37) are imposed on X ∩ (Ω_n∖Ω_{n+1}) (CRE p.261 l.8–24): every plaquette with a corner there and every bond with an end-point there (VAR p.277 l.16–17, #BC.1-1), wherever U_{p,X}, a configuration on X̂, defines them.
  - Such a plaquette p_{μν}(x), or a bond ⟨x, x + ηe_μ⟩ through REG (1.2) (p.076 l.31–47), can have its base point x in X̂∖X. #BC.6 and #BC.7 take x ∈ X only.
  - Repair, in place:
    - #BC.5 and #BC.5-3-1: w = 1 also at the points of X̂∖X on 𝒱. It holds at 𝔤-valued B near 0 by #BC.4-6, w is analytic, and the identity theorem extends it as in #BC.5-2-2.
    - #BC.6 and #BC.7: take x ∈ X̂, with Θ(x) = 1 on X̂∖X. Say that these are exactly the plaquettes and bonds at which ∂F and J(F) are defined. #BC.8 bounds Θ on X.
    - TL #6.16.3-2: replace "at x" with "at each plaquette and bond where U^d defines them, conjugated by w at the base point, with w = 1 at base points outside X". This goes in together with the BC repair, so the two stay consistent.
- ε₁'s thresholds. BC needs ε₁ < ε₁^* (#BC.4) and r_B, r_B^X ≤ log 2 (#BC.5-1). TL #94 had fixed ε₁ only by M′ε₁ ≤ a₁.
  - Since any smaller fixed ε₁ also works (the real data meet (7) with room for g small, #6.16.1-1), TL #94 now imposes both. This is applied. The text after the ε₁ sentence is split off as #94-1 at a sentence boundary.
  - TL citations of #94 for the ball and (190) are re-pointed to #94-1 (TL file lines 66, 67, 182, 199, 231 and 941). Line 339's "#94's space" keeps #94. TL is now 940d14e17be9, relabelled to 1154 tags, labels 202147b9ff81. The table fork is asked to re-point the K row (table line 157) to two-loops #94-1.
  - Queued for BC: #BC.8-5 to say "with ε₁ < ε₁^* and r_B^X ≤ log 2 (its #94)".
- #BC.2-2: the pin of the M₁-cubes of T_ξ is CRE p.256 l.58, not l.57. Queued, for before BC.2 r4. The other #BC.2 pins are re-read and hold: CRE p.245 l.32–43, p.247 l.49, p.254 l.46–51, p.255 l.12–21, p.256 l.58–63, p.257 l.7–26.
- Table fork (after launch): #T12.27's held text now states π as a definition: orthogonal for tr X*Y, with RG I printing only "the projection" (p.261 l.36–41). It is to be entered when the freeze ends, with SHAs to follow.

## Verdict: bp-crit-bc38-20261107-r2 (0 fatal, 3 serious, 11 minor)

- Read in full (reviews/bp-crit-bc38-20261107-r2/review.md, 28,492 characters). The review is context-exposed to AGENTS.md, which gives no verdict on BC.
- S1 (§1). The note never names its average. Every formula and constant (C_{BX}, δ_F) is CMP98's (43), (69), (97), (105), (106), and the count d(L − 1)/2. CRE's chain uses RG I (0.4) or (0.12) (CRE p.243 l.23–25).
  - Re-derived: RG I rejects CMP98's average because it is not Euclidean symmetric, and "preserving this symmetry is very important for the method" (p.252 l.34–36). So the reviewer's first option, choosing CMP98's average, is not open, and the steps are rederived for the chain's average.
- S2. CMP98 (131) is a step in Proposition 4's proof. It needs smallness conditions beyond c₃ (p.037 l.26, l.47).
  - Repair: (131) is no longer used. BD's #BD.9-1 bounds the chain's composed averages, under BD's ρ₀ (#BD.13).
- S3. #BC.8-5 must state the representative 𝐔 = G(V), the branch of B, and the thresholds on ε₁.
- Minor findings:
  1. #BC.8-2: the domain of v's continuation.
  2. #BC.5, #BC.5-3-1, #BC.6: "G-valued" and "Θ = 1" are proved only near 0.
  3. #BC.4-4: VAR's (∂V)(p′) is presented as a complete definition.
  4. #BC.4-3: "any set of its terms" is unexplained.
  5. #BC.4-5-2: "(19)–(21) included" is vague.
  6. #BC.5-1-3-1-1: wrong pin, p.024 l.22–28.
  7. #BC.5-2-2: wrong source for the covariance of (∂V)(p′).
  8. #BC.5-1-4: the representative of F(V) is unnamed.
  9. #BC.5-1: VAR §G's smallness of ε₁ (p.305 l.36).
  10. #BC.7-2: the spacing of 𝐉_{p,X}.
  11. #BC.8: t has two meanings.
  - Also, #BC.3-1-1 should say once that VAR's standing conditions hold with (R′, M′). This is counted with 4–5 as a wording finding.

## Repairs (bc38 r2)

- S1, the chain's average throughout.
  - #BC.1-4-1 names it: RG I (0.4) or (0.12) (p.253, p.254 l.1–3), iterated as in CMP98 (43). VAR's, CMP98's and REG's results hold for it with constants in d, L and G (RG I p.254 l.4–6; BR #BR.1-1, #BR.14-1, #BR.15). The minimal-configuration sentence is now #BC.1-4-2.
  - #BC.3-2: locality from the contours 𝐆(c₋, x), [x, x′], 𝐆(c₊, x′) (RG I p.252 l.27–32; BD #BD.11-3). #BC.4-4-3: Proposition 2 for the chain (#BR.6-3–#BR.6-4). #BC.5-1-3-2, #BC.8-2: CMP98 (69), (97), (105), (106) in chain form (#BR.4-1).
- S2, (131) and c₃ removed. #BC.5-1-3-1 takes CMP98's local axial gauge (p.024 l.22–29, p.024 l.52–p.025 l.7) on S_b, with |X₀| < (d + 2)L²B₃ε₁L^{2(j−n)}(L^jη)^{−1}. #BC.5-1-3-1-1 applies BD Step 6 (#BD.9-1) in the Hilbert–Schmidt norm, |Z| ≤ |Z|₂ ≤ √N|Z|.
  - #BC.5-1-3-3: the point averages are bounded by BR (S2) (#BR.5-2–#BR.5-5), with β from Proposition 2 at the level j.
  - The new lemma (#BC.5-1-3): C_{BX} := (24d + 8)√N under √NLt ≤ ρ₀, 4d√NLt ≤ ε, (6d + 2)√NLt ≤ ¼.
  - #BC.8: Θ(x) ≤ e^{d(t(B) + (24√N + 1)t^X)}, with no δ_F.
  - The thresholds are c^X and ε₁^* (#BC.4-1-1), and ε₁^X, ε₀^X (#BC.4-1-2).
- S3: #BC.8-5 states the principal logarithm B and the thresholds on ε₁. #BC.8-5-1 states 𝐔 = G(V), the Landau representative (TL #6.16.3-2).
- Minor findings.
  - 1, in #BC.8-2: v is continued on 𝒱.
  - 2, in #BC.5, #BC.5-3-1 and #BC.6: "near 0", and w = 1 on X̂∖X by the identity theorem.
  - 3, in #BC.4-4: VAR's definition as printed, with the uncovered bonds named.
  - 4, in #BC.4-3: every subset of the terms of (1.2).
  - 5, in #BC.4-5-2: the transformations of VAR p.278 l.15–20 and p.281 l.1–3. Criticality is the new #BC.4-5-3 (VAR (75)–(77), (82), p.290 l.34–46, p.286 l.39, p.307 l.2–3).
  - 6, in #BC.5-1-3-1: the pin is p.024 l.22–29.
  - 7, in #BC.5-2-2: covariance via RG I (0.6) and #T10.23.
  - 8, in #BC.5-1-4-1: F(V) is the axial-gauge minimal configuration.
  - 9, in #BC.5-1: VAR §G's smallness (p.305 l.36).
  - 10, in #BC.7-2-1: the spacing L^{−p} (CRE p.261 l.10, l.15–24; RG I p.262 l.49–50).
  - 11, in #BC.5-1-2 and #BC.8: t(B).
  - The wording finding is in #BC.3-1-1.
- Queued items applied:
  - the X̂∖X scope (#BC.5, #BC.5-3-1, #BC.6, #BC.7; TL #6.16.3-2);
  - #BC.8-5's thresholds;
  - the #BC.2-2 pin p.256 l.58.
- TL: #6.16.3-2, #6.16.3-2-1 (the new Θ bound) and #94 (constants depend on d, L and G for the chain's averages; citation #BC.4-1-1, #BC.5-1).
- Bookkeeping after the repairs, both re-pointed: #BC.4-1-2 cited #BC.5-1-3-1 for the norm, which #BC.5-1-3-1-1 fixes; TL #6.16.3-2-1 now cites #BC.7-2-1 and #BC.8–#BC.8-5-1.
- SHAs: BC e4152aa6f4ba, TL 68259f7645fa, labels 202147b9ff81 (1154 tags).

## Pre-check: bp-crit-bc38-20261107-r3 (full rounds of parts a and b)

- Size: #BC.3–#BC.8-5-1 is 25,576 characters, over 25k. The new content is the local gauge, BD Step 6, (S2) and criticality. Split at the proposition boundary:
  - bc38a, #BC.3–#BC.4-6, 10,635 characters;
  - bc38b, #BC.5–#BC.8-5-1, 14,941 characters.
  - Each part has the rest of BC as context. They run one at a time, b first.
- Changed lines re-read in full: #BC.1-4-1, #BC.1-4-2, #BC.2-2, #BC.3-1-1, #BC.3-2, #BC.4 through #BC.4-5-3, and #BC.5 through #BC.8-5-1.
- Re-derivations of the part-b bounds.
  - #BC.4-1-2: ε₁ ≤ ε₁^* gives 2L²B₃ε₁ ≤ a₁ and ε₀^X ≤ B₃a₁ ≤ a₀. B₃a₁ ≤ a₀ is printed in Theorem 1 (VAR p.279 l.9). Also B₃ε₁^X = 2L²B₃²ε₁ ≤ ε₀^X.
  - The local gauge: the gauge needs |b₋ − y|α₀ ≤ ½ for |A_b| < 2|b₋ − y|α₀ (CMP98 p.025 l.8). Here α₀ = L²B₃ε₁L^{−2n}, the distance is (1 + d/2)L^j steps, and (d + 2)L²B₃ε₁ ≤ 1 comes from c^X.
  - BD Step 6 holds at ρ₀, since #BD.13 imposes Steps 3, 4 and 6 at 2ρ₀. Its inputs, in the HS norm: |X|₂ ≤ √NLt(L^jη)^{−1} and |X₀|₂ ≤ √N(d + 2)L²B₃ε₁(L^jη)^{−1}.
  - (S2) at the level j: (52) at η′ = L^{−j} with α₀ = L²B₃ε₁L^{2(j−n)} ≤ c^X gives β = 2α₀ ≤ 2B₃ε₁, as j ≤ n − 1. The cube of side 3L^{j+1}η about c± and its j-blocks lie within 2.5L^nη + ½L^{n−1}η ≤ 3L^nη of z.
  - The sums: Σ_{j<n}dLa_j < 2d√NL²t/(L − 1) ≤ 3d√NLt, and Σ_{l<n}2dLa_l < 4d√NLt^X/(L − 1) ≤ 6d√Nt^X, both since L ≥ 3. Also e^x − 1 ≤ 2x for x ≤ ½, and |log(1 + Z)| ≤ −log(1 − |Z|) ≤ 2|Z| for |Z| ≤ ½. These give |B^X| ≤ 4(6d + 2)√NLt = C_{BX}Lt.
  - #BC.8-2-1–#BC.8-2-2 for F₀: B₃ε₁^X ≤ L²B₃ε₁^X ≤ c^X gives the local gauge and ρ₀ conditions. L²B₃ε₁^X ≤ ε/(80A_d) gives (S2).
  - #BC.8-4: w(x)^{−1} = G(γ)^{−1}v(y)F_L(γ)v(x)^{−1} from F = G^w = F_L^v and w(y) = 1. The norm is at most e^{12d√Nt^X + d(t + t^X)/2}, so Θ ≤ e^{d(t + (24√N + 1)t^X)}.
- Pins re-read in the corrected files:
  - VAR p.279 l.8–15, p.305 l.36, l.40–44, p.307 l.2–5, p.309 l.8–16;
  - CMP98 p.020 l.17, p.024 l.22–29, p.025 l.8, p.026 l.46–52, p.027 l.35;
  - BD #BD.6, #BD.9-1, #BD.11-2, #BD.11-3, #BD.12, #BD.13 and BR #BR.5–#BR.5-5, #BR.6-3–#BR.6-4, #BR.4-1.
- Symbols grepped across BC and TL:
  - C_{BX}, t(B), t^X, ε₁^*, ε₁^X, ε₀^X, c^X: every use agrees with #BC.4-1-1, #BC.4-1-2, #BC.5-1-3 and #BC.8.
  - δ_F and c₃ appear nowhere in BC or TL.
  - The new N is G ⊂ U(N). It clashes in letter with #T12.23's N, the number of contours, and is fixed in #BC.4-1-2.
- #T12.27 still has the old values and is marked superseded in the specs. The table fork has the new values (Peer messages).
- Tags: 95, with no duplicates and none dangling. No banned words ("gate" occurs only inside "conjugate"). LF line endings.
- Three lines run over 600 characters: #BC.4-5-2 (624), #BC.5-2-2 (618) and #BC.5-3-1 (613). Each is one argument, kept.
- Clashes found by the definition check, repaired in place (bookkeeping, no bound changed):
  - t^X is defined once, in #BC.5-1-4, and #BC.8 cites it.
  - The local field X := Ad(u)𝓗(B) clashed with the factor domain X. It is now A, with base e^{iηA₀}, and BD's X and X₀ are taken to be A and A₀. A^{(j)} would clash with #BC.1's set notation A^{(n)}, so the logarithm is BD's Φ_j(A) (#BD.9), and Q_j := L^jηAd(u(b₋))^{−1}Φ_j(A) makes the return from the gauge u explicit (#BD.11-2).
  - (S2)'s W₀, W′, a and β are instantiated ("taken to be"), not redefined. They clashed with #BC.5-1-3's W₀, and β with CRE's β in f_{m,n} (#BC.6-1).
  - In #BC.8-2-2 the point average is κ, not a, which was also (S2)'s a; q is taken in #BC.2.
  - The CMP98 pin p.025 l.7 holds in the corrected file (the uncorrected file has the bound at l.8).
- Table 0edc0267b53c (labels 379a1b76931e): the fork entered #T12.27–#T12.27-3 (Peer messages). Re-read against BC: every value agrees. The fork's own re-derivations (6d + 2, 2L/(L − 1) ≤ 3, and the square of the norm bound) agree with mine.
- bc38b spec specs/spec_bc38b_r3.json, prior r2's review: BC a473a2682148, LF f6410b35dcab. The definition check gives 0 conflicts (28 allowed). 15,120 characters are under review, 37,787 argument characters in all. The part was re-read in full after the renames.
- Known weak points: none.
- Launched 21:5x as task bqsg89523. It runs at high effort: the launch omitted -Effort medium, and the script's default is high. It is not stopped, and bc38a passes -Effort medium.
- Part a, done while bc38b runs (part a's lines are not under review in bc38b, which reads a frozen snapshot).
  - #BC.4-5-3 split at a sentence boundary. #BC.4-5-3 now says that 𝔉 is the action (41) in the variable A′ of (47) ((74), (81); VAR p.284 l.41–49, p.289 l.44–51, p.290 l.34–38), the link the step from continuity to "local minimum at 0" needed.
  - In #BC.4-5-3-1, (75) is L^jηQ_jA′ = B with B fixed, affine, kept along A′ + sδA′ by (83) (p.290 l.46–47). The earlier "(75)–(76) are linear" is gone.
  - Pins corrected against the corrected files: RG I (0.12) is p.254 l.2–6 and "all results of the paper [12] are valid for it" is l.7 (#BC.1-4-1, #BC.3-2; the table fork fixed #T12.27-3, table c1cb2d35aa43). VAR's standing conditions are p.277 l.11–17 (#BC.3-1-1), Λ_j is l.18–24 (#BC.3-1), and Proposition 2 is p.281 l.26–30 (cited p.281 l.1–30).
  - Pins re-read and holding: VAR p.278 l.2–46, p.279 l.8–15, p.281 l.1–30, p.284 l.41–49, p.286 l.39, p.289 l.44–57, p.290 l.1–4, l.30–47; CMP98 p.026 l.46–52; RG I p.252 l.7–10, l.20–36; CRE p.256 l.49–51, p.257 l.1–20.
  - Re-derived: #BC.4-3-2's 2(d − 1)B₃ε₁η^{−1} ≤ ε₀^Xη^{−1}; #BC.4-4-2's 2L^jη ≤ RM₁L^{j−1}η (RM₁ ≥ 3dL); #BC.4-4-3's α₀ = L²B₃ε₁ ≤ c^X ≤ c₂^{CMP98}, giving < 2α₀ = ε₁^X; and at j = 0, B₃ε₁ ≤ ε₁^X. #BC.4-6 uses B₃ε₁^X ≤ ε₀^X ≤ a₀ and ε₁^X ≤ a₁.
  - Part a is 10,882 characters. Spec specs/spec_bc38a_r3.json, prior r2's review; the definition check gives 0 conflicts (6 allowed). It is built and launched with -Effort medium once bc38b is triaged.
  - After bc38b r3's triage, the only change in part a is #BC.4-1-2's re-pointed tag (#BC.5-1-3-1-2, the norm), re-read. Part a has no wording of inference, reading or omission. BC is be21708f0738, LF ff32ad403ddb, table e720ca74ed6c. The definition check gives 0 conflicts (6 allowed). Part b's repaired lines are context in this round.

## Queued during bc38b r3 (part b's lines wait)

- #BC.5-1-1: the pin "p.305 l.30–42" becomes p.305 l.31–43 ((172) is l.31–36 in the corrected file, and (173) and C₁'s constancy are l.39–44).
- Applied outside part b: #BC.1-4-2's pin of (172) is now p.305 l.31–36. In BP_LFR2_REPLACEMENT.md #160.3, the ball (172) is stated as printed, |V′ − 1| < C₁ε₁, and is no longer described as "radius 2C₁ε₁", which is its consequence |B′| < 2C₁ε₁. V′ = e^{−ig_kB′} lies in it for g small. The pre-read of the LFR2 replacement for its first round has started.
  - #160.1–#160.2-1's LFR II p.365 pins hold ((1.33) l.2–6, (1.34) l.10–13, (1.35) l.16, l.35–36), and so does p.356 l.37 (|B′| < M₀g_k^{−1}ε_k).
  - #160.2-2: LFR I (1.79) p.195 l.5–8, (1.86) p.197 l.24–27 and LFR II (1.50) p.370 l.3–5 hold. The compensation sentence is p.197 l.39–41, not l.38–40, and is re-pointed.
  - #160.7: LF #4.44-0 (dist_sup(Λ, Z^c) ≥ 8MR_k) and #4.48-3.0.1 hold.
  - Every TL tag cited (39) exists. The file is BP d1781343c331 before these two pins.

## Verdict: bp-crit-bc38b-20261107-r3 (0 fatal, 0 serious, 8 minor)

Full round of part b (#BC.5–#BC.8-5-1). The round ran at high effort, not medium (launch flag omitted). Not clean: 8 minor. Its verdicts: #BC.5, #BC.6–#BC.7 and #BC.8 are correct.

| # | Finding | Repair |
|---|---|---|
| 1 | The trace normalisation of the norm with subscript 2 is unstated; with CMP98's tr, which is normalised, the inequality fails | #BC.5-1-3-1-2 takes the Frobenius norm with Tr unnormalised (CMP98's tr of (17) is N^{−1}Tr), so the norm without subscript is at most the Frobenius norm, which is at most √N times it |
| 2 | B^X (#BC.5-1-3, #BC.5-1-4-1) and B (#BC.8-5) not stated 𝔤^c-valued | #BC.5-1-3's statement adds it. #BC.5-1-3-4-1 proves it: the hypotheses' B form a ball; at 𝔤-valued B near 0, B^X ∈ 𝔤; the orthogonal component is analytic and vanishes on an open set of real points. #BC.5-1-4 records it. #BC.8-5 obtains B from VAR (172) (p.305 l.31–36, p.307 l.2, p.309 l.11), and #BC.8-5-1 identifies it with the principal logarithm by the injectivity of exp |
| 3 | The transfer of CMP98's local axial gauge to S_b is unstated | New #BC.5-1-3-1-1. CMP98's bound for a bond b′ (p.025 l.7) uses only the plaquettes of the coordinate box spanned by y and b′₊; for y = b₋ and b′ ⊂ S_b that box lies in S_b |
| 4 | #BC.8-2-1: (d + 2)B₃ε₁^X ≤ 1 and v = 1 on Λ^X_0 uncited | (d + 2)B₃ε₁^X ≤ (d + 2)c^X ≤ 1 (#BC.4-1-2); v^X = 1 on Λ^X_0 (VAR p.281 l.2) |
| 5 | #BC.5-1-3-2 asserts analyticity by forward reference | The sentence moved to #BC.5-1-3-4, after both sides' bounds, and #BC.5-1-3-4-1 carries the identity from real B near 0 to the ball |
| 6 | #BC.7-2-1: the spacing of 𝐉_{p,X} is an inference | It is the definition. CRE p.260 l.54–55 and p.261 l.2 define CRE's spaces "similarly as in (I.1.11)–(I.1.16)", and RG I (1.15) defines J_n by (1.8) with U_n and L^{−n} (p.262 l.49–50). The table fork entered it as #T6.11-1 (table 3b28dde0e875), which #BC.7-2-1 cites |
| 7 | #BC.8-5: §G's smallness must also cover ε₁^X | It now covers ε₁ for 𝐁 and ε₁^X for 𝐁^X |
| 8 | Symbol clashes: β, ρ, u, v | (S2)'s β is "its plaquette bound" (#BC.5-1-3-3, -3-1, #BC.8-2-2); 𝒱's radius is r_𝒱; the local gauge is σ_b; #BC.8's v is v^X. None of these clash with the table |

Also:
- #BC.7's π is RG I's projection (p.261 l.40). No orthogonality is used: CMP98 (17) prints only the scalar product (the table fork's check). #BC.7-1 now takes the covariance J(Y^u)(b) = R(u(b₋))J(Y)(b) as RG I (3.42) applies it at G^c-valued u (p.278 l.47–52), with locality from REG (1.1)–(1.2). The earlier unitarity argument and the remark that RG I names no complement are deleted. The table fork was asked to make #T12.27 read the same.
- Stale tags re-pointed: #BC.4-1-2 to #BC.5-1-3-1-2; #BC.5-1-3-4 and #BC.8-2-1 to #BC.5-1-3-1-3. #BC.8-5-1 is now #BC.8-5-2, and TL #6.16.3-2-1 cites #BC.8–#BC.8-5-2.
- TL wording: #6.12.1-1 takes p = 1, …, j from RG I (iv) through CRE's definition; #94-1 says "(172) is |V′ − 1| < C₁ε₁, under which |B′| < 2C₁ε₁"; #94-1's status sentence on (190) is cut to its citation.
- Checks: 99 tags, no duplicates, nothing dangling; the remaining long lines are 613–624 characters; the "gate" hits are "conjugate"; the cross-file tags all resolve. Part b is 16,229 characters.
- SHAs: BC f1bcdf0d0978, TL 0bcd0326c6f8, LFR2 525a536d7b52.
- Bookkeeping (no round), during bc38a r3 and in part b only, after the table fork's clash notes (table 08319731956f): the configuration G(V) is renamed U_L(V), with U_L(γ), U_L(b), U_L^w, ∂U_L, J(U_L) and Ū_L^n, separating it from the group G; #BC.8-2-2's holonomy P is renamed h_l, separating it from #BC.6's plaquette P. a_j, a_l, w and F are kept, since they match BR (S2)'s a and TL's w. BC 39781aab429b. bc38b r4 sees the renames.

## Verdict: bp-crit-bc38a-20261107-r3 (0 fatal, 0 serious, 6 minor)

Full round of part a (#BC.3–#BC.4-6), medium effort. Not clean: 6 minor. Its verdicts: #BC.3 and #BC.4 are correct, and every r2 finding on part a is repaired.

| # | Finding | Repair |
|---|---|---|
| 1 | "Critical" in VAR is presented as a definition; the chart image of U⌈X and the line's membership in 𝔘 ∩ 𝔙 are unstated | #BC.4-5-3 gives the chart: Proposition 2 is one-to-one into (19)–(21) for ε₀ + C₁ε₁ ≤ c₁ (p.281 l.1–30), and (47)'s range contains (43) for ε₂ ≤ ¼ε₃ (p.289 l.30–35, p.290 l.6–8), both secured by a₀, a₁ small (p.280 l.42). New #BC.4-5-3-1 states what VAR proves: 𝔉 has exactly one critical point on (75)–(77), in VAR's printed sense (82)–(83) (p.290 l.34–47), the image of the minimal orbit (p.281 l.32–34). #BC.4-5-3-2–#BC.4-5-3-3 take A′_X, and Y_s ∈ 𝔙 by (75), (48) and (20), and Y_s ∈ 𝔘 by openness. #BC.4-5's statement and #BC.4-6 use the critical point |
| 2 | VAR's M₁ (= M′) clashes with CRE's M₁ = KM′ of #BC.2 | #BC.3-1-1, #BC.4-2 and #BC.4-4-2 write R′M′ and M′ |
| 3 | One set a₀, a₁, B₃ for 𝐁 and 𝐁^X is unstated | #BC.3-1-1: they depend only on d and L once R₁, M₁ are fixed (p.277 l.17, p.279 l.28), and on G (#BR.1-1); one choice at the cube parameter M′ (#T2.7) serves both |
| 4 | #BC.4-5-2 cites p.281 l.1–3 for invariance of 𝔙; 𝔘's invariance under the subsets is unargued | New #BC.4-5-2-1 uses only VAR (4) (p.278 l.15–20): plaquette norms are conjugation-invariant and t_ν(U^u) = R(u(x))t_ν(U) with R(u(x)) an isometry |
| 5 | #BC.3 omits the domain of M_𝐁; #BC.3-2 does not say why [x, x′] stays in Δ(c₋) ∪ Δ(c₊) | #BC.3 takes configurations at which the averages are defined (RG I p.253 l.15). #BC.3-2 says Ū^{n−1} along c is the product over its L bonds; new #BC.3-2-1 proves the containment coordinatewise |
| 6 | Citations and wording | #BC.3-1 cites #BC.1-4-1; #BC.4-3 says "bond with an end-point in X" and names the plaquettes at which U⌈X(∂p) is defined; #BC.4-6 cites #BC.3-1-1 and #BC.4-1-2; "(83): QδA′ = 0 and RD*δA′ = 0"; the Frobenius norm is defined in #BC.4-1-2, and #BC.5-1-3-1-2 cites it |

- New tags: #BC.3-2-1, #BC.4-5-2-1, #BC.4-5-3-1 (VAR's uniqueness) and #BC.4-5-3-3; the old #BC.4-5-3-1 is #BC.4-5-3-2 (cited nowhere outside BC and this file).
- Checks: 103 tags, no duplicates, nothing dangling; long lines 604–633 characters; "gate" hits are "conjugate"; TL's 8 BC tags resolve. Part a is 12,790 characters, part b 15,954.
- Pins re-read: VAR p.277 l.11–24, p.279 l.8–28, p.280 l.1–48, p.281 l.1–34, p.285 l.1–5, p.289 l.26–57, p.290 l.1–8, l.30–47; RG I p.253 l.1–16.
- SHAs: BC 94ef477ef739, table d8006ecd710f, LF 11ce11342b9a.

## Pre-check: bp-crit-bc38b-20261107-r4 and -r4h (full round of part b, two referees)

- At the user's request, one build is reviewed by two referees: r4 at medium effort, r4h at high. Both specs (specs/spec_bc38b_r4.json, spec_bc38b_r4h.json) differ only in rev. Both are built from BC 94ef477ef739 with no edit between the builds. Their findings will be compared item by item.
- Scope: #BC.5–#BC.8-5-2, 15,954 characters. Prior: the r3 review of part b. Part a's r3 repairs are context.
- Part b changes since r3's verdict: the r3 repairs (table above), the renames U_L(V) and h_l, and #BC.5-1-3-1-2 now cites #BC.4-1-2's Frobenius norm. Re-read in full.
- Spec updated: the named steps add #BC.5-1-3-1-3, #BC.5-1-3-4-1 and #BC.8-5-2. The questions cite σ_b, v^X, U_L(V), #T6.11-1 and RG I (3.42). The transcription list adds RG I p.278 and CRE p.260. allow_defs renames G(V) to U_L(V) and P to h_l, moves |Z|₂ to #BC.4-1-2 and adds V′ (#BC.8-5). The definition check gives 0 conflicts (29 allowed).
- Known weak points: none.
- Built twice; the snapshots' BC are both 94ef477ef739 and the arguments are identical. Launched 22:35: r4 as task boqg5bu47 (effort medium), r4h as task btho5khfz (effort high), per cli.progress.

## Verdict: bp-crit-bc38b-20261107-r4 and -r4h (0 fatal, 0 serious; 9 and 8 minor)

Full round of part b (#BC.5–#BC.8-5-2) on one build, r4 at medium effort and r4h at high. Not clean. Both find #BC.5–#BC.8 correct, and both mark the caller's facts (#167-3, #94, #94-1, #6.16.1-1, #6.16.3-2, #6.16.4-2) as outside the snapshot.

| # | Finding | r4 (medium) | r4h (high) | Repair |
|---|---|---|---|---|
| 1 | #BC.5-1-3-1-1: "the box spanned by y and b′₊" | correct, presented as printed | INCORRECT when b′₊ lies between y and b′₋ | The loop Γ_{y,x} ∪ b′ ∪ (−Γ_{y,x+e_μ}) is written out; its plaquettes lie in the box spanned by y, b′₋ and b′₊ (CMP98 p.024 l.52–p.025 l.2); new #BC.5-1-3-1-1-1 places it in S_b |
| 2 | "≤ ½" presented as printed | yes | yes | Stated as the condition of the logarithm bound, with ½(d + 2)L²B₃ε₁ ≤ ½ derived |
| 3 | Bondwise convention of Ad(σ_b) | yes | no | A(b′) := Ad(σ_b(b′₋))𝓗(B)(b′) (CMP98 (55), p.027 l.2–8; #BD.11-2) |
| 4 | #BC.5-1-3 omits B smaller than r_B | yes | yes | Added to the hypotheses |
| 5 | Source of (d + 2)L²B₃ε₁ ≤ 1 | yes | yes | (d + 2)c^X ≤ 1 (#BC.4-1-2) |
| 6 | #BC.5-1-3-1-3 should cite #BR.11-1 | yes | no | Cited |
| 7 | #BC.5-1-3-4-1: the ball may be closed | yes | yes | Identity theorem on the interior, continuity on the ball |
| 8 | #BC.8-5-1: radius of exp's injectivity | yes | no | B smaller than 2C₁ε₁ ≤ 4 log 2 < π (#BC.5-1), so iB is the principal logarithm of V′ |
| 9 | #BC.8-5-2: restriction to defined plaquettes and bonds; cite #BC.6-1, #BC.7-2-1 | yes | no | Both added |
| 10 | Spacing of 𝐉 in (U_L(V), J(U_L(V))) | no | yes | #BC.7-2-1 and #BC.8-5-2: 𝐉 is the current at the spacing ξ, with (ξ/η)³𝐉 = J(U_L(V)) (#BC.7-2) |
| 11 | π's equivariance; partly defined bonds | RG I (3.42)'s G^c attribution unverified | equivariance unstated, drawn from (3.42) | π is RG I's projection onto 𝔤^c (#T12.27), orthogonal for CMP98 (17)'s tr X*Y, as RG I names no complement. #BC.7-1 proves R(u)π = πR(u) for G-valued u, and that Im commutes with R(u); the G^c attribution is dropped. New #BC.7-1-1 holds the continuation and the partly defined bonds |
| 12 | Symbol clashes | f, Q_j, a_j | Q_j, a_j, u | 𝔮_j, 𝔞_j (neither in the table); the factor is unnamed; #BC.8-2 calls v^X CMP98's transformation of (106) |
| 13 | Citations | no | CMP98 p.027 l.2 for the chain's covariance; REG p.088 l.37–38 | RG I (0.6) and #T10.23; REG p.088 l.37. #BC.6's REG p.077 pin is l.49 |
| 14 | Table #T12.27-5's Ḡ | yes (out of scope) | no | Sent to the table fork |

- Comparison: r4h alone found the one false sentence (item 1), the 𝐉 spacing and π's equivariance. r4 alone found five citation and wording points (items 3, 6, 8, 9, 14). Neither is a subset of the other.
- New tags: #BC.5-1-3-1-1-1, #BC.7-1-1. Checks: 105 tags, no duplicates, nothing dangling; long lines 601–633 characters; "gate" hits are "conjugate". Part b is 17,304 characters.
- Pins re-read: CMP98 p.020 l.31–35, p.024 l.52–p.025 l.7, p.027 l.2–14; REG p.077 l.38–54, p.088 l.37; RG I p.261 l.34–48, p.262 l.41–56, p.278 l.40–52.
- SHAs: BC 94ef477ef739 → c2750fd86b4b.

## Pre-check: bp-crit-bc38a-20261107-r4 and bp-crit-bc38b-20261107-r5 (full rounds of parts a and b)

- Both are medium effort, built from BC c2750fd86b4b, LF ac2ca2e06f71 and table 8ef253caa3d3. Specs: specs/spec_bc38a_r4.json and spec_bc38b_r5.json.
- bc38a r4 covers #BC.3–#BC.4-6, 12,790 characters. Its prior is the r3 review of part a. Part a has not changed since r3's repairs. The named steps add #BC.3-2-1, #BC.4-5-2-1 and #BC.4-5-3-1–#BC.4-5-3-3. Q5 asks about the chart (Proposition 2, (47)) and VAR's unique critical point (82)–(83).
- bc38b r5 covers #BC.5–#BC.8-5-2, 17,304 characters. Its prior is r4h's review, and Q2 lists r4's further points. The named steps add #BC.5-1-3-1-1-1 and #BC.7-1-1. Q3 asks about the loop and box of CMP98's gauge. Q6 asks about π's orthogonality for CMP98 (17) and the commutation proof. allow_defs adds 𝔮_j, 𝔞_j, 𝔞_l and A(b′).
- Definition checks: 0 conflicts each (7 and 32 allowed).
- Known weak points: none. π's orthogonality is a definition here: RG I prints only the target 𝔤^c. It is stated as such in #BC.7 and in #T12.27.
- Built at 23:06 with LF 37d0c64728e2; the LF moved twice during the build, so the pin is the build-time one. Both snapshots hold BC c2750fd86b4b. Launched at 23:06:46: bc38a r4 as task b5yimo48y and bc38b r5 as task bzzvzw4pd, both at medium effort, per cli.progress. The user stopped both runs at once. Their folders are built but hold no review, and neither part is launched again until the user says so.
- User, 23:15: "Run referees on high from now on!" This replaces the earlier medium-effort rule. Every later referee runs at effort high, one at a time.
- bp-crit-bc38b-20261107-r5h replaces r5. It uses the same spec (specs/spec_bc38b_r5.json, rev renamed), with a shorter output format in the scope:
  - a CORRECT step gets one line, naming the check made;
  - each finding is stated once, in its own step entry;
  - each question gets one or two lines, citing tags;
  - the disclosure is one line per source;
  - the ranked list appears once.
- The format was changed at the user's request, after r4h's 388-line review stated each finding three or four times. Built at 23:16 with BC c2750fd86b4b, LF d7604c80f69f and table c4d22ad1414e; the definition check found 0 conflicts. Launched at 23:16:18 as task b0y63d7my, effort high. The user stopped it. Nothing is running now.

## Pre-check: bp-crit-bc38-20261107-r5 (#BC.3–#BC.8-5-2 as one package, effort high)

- User, 23:20: "Review them as one package!" The halves are reviewed together. That is about 30k characters under review, above the workflow's 25k limit, which this instruction overrides for this packet.
- Spec: specs/spec_bc38_r5.json, built from BC c2750fd86b4b and LF d7604c80f69f. Its prior is r4h's review of part b. Q1 also lists r4's findings and those of part a's r3. The named steps are the union of both parts, including #BC.5-1-3-1-1-1 and #BC.7-1-1. The scope uses the short format: one line for each CORRECT step; each finding stated once; one or two lines per question; the ranked list once.
- Definition check: 0 conflicts (38 allowed).
- Known weak points: none. π's orthogonality is a definition, since RG I prints only the target; #BC.7 and #T12.27 say so.
- Each half's clean count restarts with this round. A clean result needs two consecutive clean rounds of the package, the second full.
- Launched at 23:18:51 as task bc21oq4po, effort high, per cli.progress.

## Verdict: bp-crit-bc38-20261107-r5 (0 fatal, 0 serious, 8 minor)

One package, effort high, finished at 23:35:56; 238 lines. Not clean. Every other step and all questions are marked correct.

| # | Finding | Repair |
|---|---|---|
| 1 | #BC.3-1-1: no source for 𝐁's VAR conditions at (R′, M′) | New #BC.3-1-1-1: Ω_n is a union of M′L^nη-cubes (#BC.2-1-2, #BC.2-1-3), and (L^nη)^{−1}dist(Ω_n^c, Ω_{n+1}) ≥ 2MR_n ≥ 2M (BP_LAYER_WIDTHS.md #4.18; CRE p.256 l.21–24, (2.1), (2.5)) > R′M′, as R′M′ < LM₁ ≤ M/L |
| 2 | #BC.4-5-2-1: 𝔙 invariance stated for every u | Restricted to transforms (U⌈X)^u in 𝔙(𝐁^X, W); then u(c₋)W(c)u(c₊)^{−1} = W(c) at every datum, by the covariance of the averages (RG I (0.6); #T10.23), so u keeps 𝔙(𝐁^X, W) |
| 3 | #BC.4-5-3: base U₀ unnamed and clashing with #BC.5-1's U₀; the a₀, a₁ sentence a reading | U₀^X := VAR's base for 𝐁^X (U_{m−1}(V₀), or V₀ at m = 1), satisfying (14) with C₁^X := L³max{1, 4d/B₃}: by p.280 l.20 for m ≥ 2, and checked from (7) and (11) at m = 1. Both conditions of the chart are now imposed through ε₁^*: c^{VAR} := min{c₁, ε₃/(4B₁)} and ε₀^X + C₁^Xε₁^X ≤ c^{VAR} (#BC.4-1-1, #BC.4-1-2), with ε₂ := B₁(ε₀^X + C₁^Xε₁^X) ≤ ¼ε₃ (new #BC.4-5-3-0) |
| 4 | #BC.4-5-3-3: "the return to the axial gauge" undefined | Y_s := U′U₀^X, U′ the transform (16) of e^{iηA_s} by CMP98 (106)'s u, determined uniquely by U₁ (REG p.088 l.36) and inverting U₁ = U′^{u^{−1}} (VAR p.281 l.1–4); (20) is REG (1.31) (VAR p.281 l.11–14), REG's form of (1.30) (REG p.082 l.3–13). Split into #BC.4-5-3-3-1 |
| 5 | #BC.5-1-3-4: forward dependence; domain of the complex averages implicit | B^X(c) is defined as (1/i)log of #BC.5-1-3-2's right side; #BC.5-1-3-4-1 defines the complex averages of U_L(V) as the analytic continuation, as for U_𝐁 (#BC.1-4-2); new #BC.5-1-3-4-2 holds the 𝔤^c argument |
| 6 | #BC.5-3-1: "G^c-valued" not argued | #BC.5 states invertible values; new #BC.8-4-1 proves G^c-valuedness: η𝓗, η𝓗^X, log h_l, log κ are 𝔤^c-valued by the identity theorem, and G^c = e^{i𝔤^c} is a group containing G (CMP98 p.020 l.30–31) |
| 7 | REG pins of #BC.6, #BC.7-1, #BC.8-2 one line late | Printed lines: p.077 l.48, (1.11) at p.077 l.48–52, p.088 l.36 |
| 8 | Table #T12.27-6 still has e^{iQ_l} | Sent to the table fork |

- New tags: #BC.3-1-1-1, #BC.4-5-3-0, #BC.4-5-3-3-1, #BC.5-1-3-4-2, #BC.8-4-1. New symbols U₀^X, C₁^X, c^{VAR}; the table has none of them (c^V_j exists, so c^V was not used).
- Checks: 110 tags, no duplicates, nothing dangling; long lines 601–634 characters; "gate" hits are "conjugate".
- Pins re-read: VAR p.277 l.11–17, p.279 l.9–28, l.43–50, p.280 l.2–53, p.281 l.1–22, p.290 l.1–9, p.307 l.2–5, p.309 l.8–14; CRE p.254 l.46–51, p.255 l.36–38, p.256 l.21–24; REG p.081–p.082 (1.28)–(1.31), p.088 l.36; CMP98 p.020 l.30–31; BP_LAYER_WIDTHS #4.18.
- SHAs: BC c2750fd86b4b → 903c050ea6ba → da430c5d1b3b (#BC.4-5-3-0 names VAR's ε₂ without redefining it). TL after the #55 edit: 58345871948f. The table fork entered the new symbols in #T12.27-1 and #T12.27-1-1, 𝔮_l in #T12.27-6, and w's G^c values (#BC.8-4-1); table 5c65dc108348.

## Pre-check: bp-crit-bc38-20261107-r6 (one package, effort high)

- Spec: specs/spec_bc38_r6.json, from r5's spec with BC da430c5d1b3b and LF 9186fbbbf1be. BP_LAYER_WIDTHS #4.18 is added as permitted background, and REG's pages extend to p.082. Definition check: 0 conflicts (42 allowed). Its prior is r5's review. Q1 lists r5's eight findings and asks whether each repair holds. The named steps add the five new tags.
- Q2 asks whether C₁^X and the m = 1 check of (14) are right, and whether c^{VAR} enforces both of the chart's conditions. Q3 asks whether #BC.8-4-1's identity-theorem argument gives G^c values on all of 𝒱.
- Known weak points: none. The clean count restarts: two consecutive clean rounds of the package, the second full.
- Launched at 23:51:13 as task b5v6ulu2b, effort high, one referee, per cli.progress.

## Verdict: bp-crit-bc38-20261107-r6 (0 fatal, 0 serious, 8 minor)

One package, effort high; 265 lines. Not clean. Every step is marked correct, and Q2–Q8 are answered yes.

| # | Finding | Repair |
|---|---|---|
| 1 | #BC.4-5-3: "top index m" of 𝐁^X indeterminate | m^X := the top index of 𝐁^X; m^X = 0 is the trivial case (#BC.4-6, #BC.5-1-4-1, #BC.8-1, #BC.8-4), and m^X ≥ 1 is used in #BC.4-5-3 with U₀^X := U_{m^X−1}(V₀), or V₀ at m^X = 1 |
| 2 | #BC.4-5-3-2, #BC.4-5-3-3-1: reality of δA′ and G-valuedness of Y_s unstated | New #BC.4-5-3-2-1: at G-valued U₀ the operators of (44)–(61) preserve 𝔤-valuedness (REG p.080 l.10–12, p.082 l.14, l.52). New #BC.4-5-3-2-2: H is the real minimiser (VAR p.285 l.19–20), and D and X are limits of 𝔤-valued iterates of the contractions (50), (61) (p.286 l.20–21, p.287 l.14–25). So A_s is 𝔤-valued, Y_s is G-valued by CMP98 p.033 l.39–45, and (82) extends by ℂ-linearity, as (83) is conjugation-invariant (#BC.4-5-3-3-2) |
| 3 | #BC.3-1-1-1: the 2MR_n separation is for step domains only | Every layer of 𝐁_k is at least M wide in its units: step layers by CRE p.256 l.21–24, (2.1), (2.5), and R-operation layers by induction over the times (BP_LAYER_WIDTHS.md #4.18, #4.18-2-1) |
| 4 | #BC.8-4-1: CMP98's "image of exp is a subgroup" is false for SU(N) | G^c := the subgroup of GL(N, ℂ) generated by e^{i𝔤^c}, so the proof stands. New #BC.8-4-1-1 gives the SU(2) counterexample to the printed claim |
| 5 | #BC.5-1-3-1-2, #BC.5-1-3-1-3: 𝔤^c-valuedness of A and 𝔮_j not stated before use | Stated where BD Step 6 and (S2) are applied: A by #BC.8-4-1, as Ad(G) preserves 𝔤^c, and A₀ 𝔤-valued; 𝔮_j 𝔤^c-valued by #BC.8-4-1 |
| 6 | #BC.5-1-3-4-1: definition versus identity of the complex averages unclear | The averages are RG I's, analytic on sets of G^c elements of small diameter (RG I p.253 l.14–16). New #BC.5-1-3-4-1-1 computes them through ψ of (I4) and BD Step 3 at 2ρ₀ (#BD.6-2–#BD.6-3, #BD.13). #BC.5-1-3-4-2 proves #BC.5-1-3-2 on the ball by the identity theorem |
| 7 | #BC.7-1: comma splice | The last sentence now reads "REG (1.11) then gives J(Y^u)(b) = R(u(x))J(Y)(b), the covariance that RG I uses at (3.42)" |
| 8 | #BC.5-1-4: strict/non-strict clash | r_𝒱 ∈ (0, r_B), with the hypotheses for every B of norm at most r_𝒱, and 𝒱 the open ball of radius r_𝒱 |
| 9 | Table #T12.27-6 writes e^{iQ_l} | The table row was re-read. It already writes 𝔮_l (mirrored after r5), so nothing needed changing |

- New tags: #BC.4-5-3-2-1, #BC.4-5-3-2-2, #BC.4-5-3-3-2, #BC.5-1-3-4-1-1, #BC.8-4-1-1, plus sentence-boundary splits of over-long lines. New symbol m^X. G^c is redefined as the generated subgroup. The table fork entered both (table aae8e3d40319).
- Re-read during the recheck: CRE (2.5) is restored in #BC.3-1-1-1. #BC.8-4-1 uses the ball, not 𝒱, for the B-chart objects. The r_ψ condition is added in #BC.5-1-3-4-1-1. "Minimum" is changed to "minimiser". D*'s reality is stated. The m^X = 0 case is carried through.
- Pins re-read: VAR p.278 l.15–20, p.279 l.13–15, l.43–50, p.280 l.2–53, p.281 l.1–34, p.284 l.41–49, p.285 l.19–20, p.286 l.2, l.20–21, l.39, p.287 l.14–25, p.289 l.30–57, p.290 l.2–47, p.307 l.2–5; REG p.076 l.31–47, p.077 l.48–52, p.080 l.10–12, p.082 l.3–14, l.52, p.088 l.36; RG I p.253 l.14–16, p.278 l.47–52; CMP98 p.020 l.30–31, p.033 l.39–45; BD #BD.3-3, #BD.6-2–#BD.6-3, #BD.9-1, #BD.13.
- TL #169: c_π is now the map's sup{‖dπ(Y)‖ : Y ∈ 𝔤, ‖Y‖ ≤ 1} in the operator norm (#MOSTC.2-4, #T12.13-1), the same as the table fork's mismatch report (fix (a)). TL 4dcc8ac2b48e. The change goes to TL's next content round.
- SHAs: BC da430c5d1b3b → 3405412518a5 → 2c6ce50f8386 (#BC.5-1-3-4-1-1: η|A₀|₂ < ρ₀L^{−n} strictly, from #BC.5-1-3-1's strict bound, so ψ lies in the interior of Step 3's domain and #BC.5-1-3-4-2's continuity on the ball holds). Table aae8e3d40319 → 31436db32f84 (only #T12.9's pointer, per the fork).

## Pre-check: bp-crit-bc38-20261107-r7 (one package, effort high)

- Spec: specs/spec_bc38_r7.json, from r6's spec with BC 2c6ce50f8386 and LF 0f55157a095f. Definition check: 0 conflicts (43 allowed; Ω^X_{m^X+1} added). Its prior is r6's review. Q1 lists r6's eight findings and asks whether each repair holds. The named steps add the new tags.
- Every changed line was re-read. These uses were grepped and fixed in the same pass: m^X (#BC.4-5-3, #BC.4-6, #BC.5-1-4-1, #BC.8-1, #BC.8-4), G^c (#BC.5, #BC.5-1-3-1-2, #BC.5-1-3-1-3, #BC.5-1-3-4-1, #BC.8-4-1), ψ (#BC.5-1-3-4-1-1, #BC.8-4-1), and the hypothesis 2√NLt(B) ≤ ρ₀ (#BC.5-1-3, #BC.5-1-3-1-2, #BC.5-1-3-4-1-1). There is no circularity: #BC.8-4-1's 𝔤^c-valuedness of 𝓗 uses #BC.5-1-1 alone, and that of ψ uses only ψ's analyticity.
- Domains: on the hypothesis ball, ψ is strictly inside Step 3's domain at 2ρ₀, 𝔮_j at Step 6's ρ₀ is inside the 2ρ₀ domain, and (S2)'s f is analytic on |t| ≤ R₀ with R₀ ≥ 2 > 1. So both sides of #BC.5-1-3-2 are analytic on an open set containing the ball.
- Sizes: part 36281 characters (the package overrides the 25k limit, per the user), context 12279. 117 tags, no duplicates, nothing dangling. Long lines run 601–634 characters. The "gate" hits are "conjugate".
- Known weak points: none. The clean count restarts: two consecutive clean rounds of the package are needed, the second full.
- Built at 00:32:38 (table 31436db32f84, labels c4013f2c7f07, 13 balaban_proofs files frozen). Launched at 00:32 as task b2gd0zeua, effort high, one referee.

## Verdict: bp-crit-bc38-20261107-r7 (0 fatal, 0 serious, 5 minor)

Not clean; the clean count stays at zero. Every other step is CORRECT. M1 comes from my r5 repair (C₁^X), M2 from my r6 split (#BC.4-6-1 was not added to the extract). M3–M5 are older text that was already in the r5 snapshot.

| # | Finding | Repair |
|---|---|---|
| 1 | #BC.4-5-3-1: VAR's uniqueness is cited without its printed hypotheses 8ε₂ ≤ a₄ and 2B₀C₁B₃ε₁ ≤ 8ε₂ (p.296 l.8–10), which VAR absorbs only for its own C₁ | c^{VAR} := min{c₁, a₄/(8B₁), ε̄₃/(4B₁)}, ε̄₃ VAR's ε₃ (new #BC.4-1-1-1), in ε₁^*'s third entry with C₁^Xmax{1, B₃}. New #BC.4-5-3-0-1: ε₂^X := B₁(ε₀^X + C₁^Xmax{1, B₃}ε₁^X), ε₃^X := 4ε₂^X. #BC.4-5-3-1 states the hypotheses, and new #BC.4-5-3-1-1 checks them: (113), 8ε₂^X ≤ a₄, 8ε₂^X ≥ 2B₀C₁^XB₃ε₁^X, and (103) |
| 2 | The extract ends at #BC.4-6 and omits #BC.4-6-1 | The r8 extract ends at #BC.4-6-1 |
| 3 | #BC.5-1-3-1-1-1 cites CMP98 (55), the fixed-V₀ form | VAR (17) (p.280 l.34–37), REG (1.18) (p.078 l.50–54) and #BD.11-2 |
| 4 | #BC.5-1: VAR §G's smallness is not stated | New #BC.5-1-0: C₁ε₁ ≤ ½ for (172)'s logarithm, and B₅ε₁ ≤ B₁c^{VAR}. So Sects. A–E apply to the pair with VAR's ε₂ the value of (173) and ε₃ = 4ε₂: the chart, 8ε₂ ≤ a₄, ε₃ ≤ ε̄₃, 2B₀C₁B₃ε₁ ≤ 8ε₂ and (103). The same holds with ε₁^X. #BC.8-5 and TL #94 cite it |
| 5 | #BC.4-4: the j = 0 bonds with both end-points outside X are not listed as uncovered | Added to the uncovered bonds in the same sentence |

- Re-read during the pre-check, and repaired: #BC.5-1-0's first version took ε₂ = B₅ε₁ and imposed only 4B₅ε₁ ≤ ε̄₃ and 8B₅ε₁ ≤ a₄. That missed the chart's ε₀ + C₁ε₁ ≤ c₁, and (103) would have needed 24B₃ > 1. Both hold with (173)'s ε₂ and B₅ε₁ ≤ B₁c^{VAR}: ε₂/B₁ = ε₀ + C₁ε₁ ≤ c^{VAR}, 8ε₂ ≥ 32B₁B₃C₁ε₁, and ε₃ ≥ 4B₁C₁ε₁. Also fixed: #BC.4-5-3-0-1's "Both conditions" (there are three), and #BC.4-5-3-1-1's citation of (113), which is now #BC.4-5-3-0-1. The ":=" on VAR's own ε₂, ε₃ and U′ became "take VAR's ε₂ to be" and "U′ =", since these choose VAR's parameters and define no new symbols.
- BR fecfa5745a94 (BETA's note) was re-derived against BC. VAR's B₃ is (162) (p.303 l.36–41), and #BR.14-3 multiplies it by K_{B₃}, which depends on G. #BC.3-1-1-2 now cites p.303 l.36–41 and #BR.14-3. c₂^{CMP98} = min{1/(3C₀^{ch}), c₂′^{ch}/2} (#BR.6-4) is still the chain's Proposition 2 threshold, so #BC.4-1-2 and #BC.4-4-3 hold as written. B₅ = 6B₁B₃C₁ (p.305 l.41) enters only as a symbol. No bound in BC changes.
- Pins re-read: VAR p.280 l.33–37, p.289 l.28–36, p.290 l.1–9, p.292 l.44–52, p.293 l.28–42, p.294 l.28–56, p.295 l.44–52, p.296 l.1–20, p.303 l.10, l.36–41, p.305 l.28–56; REG p.078 l.50–55.
- The table fork entered #T12.27-1-1 (c^{VAR}, ε₂^X, ε₃^X, ε̄₃) and #T12.27-1's ε₁^* (table 712c154a27ae, then dea9743123b4 with BETA's rows). #BC.5-1-0 defines no symbol.
- SHAs: BC 2c6ce50f8386 → 8606a0cef5bc → d7cb3e924234; TL 4dcc8ac2b48e → 6c97421f37d0 (#94 cites #BC.5-1-0). The TL change goes to TL's next content round.

## Pre-check: bp-crit-bc38-20261108-r8 (one package, effort high)

- Spec: specs/spec_bc38_r8.json, from r7's spec with BC d7cb3e924234 and LF 9862073671bf; BC cites no LF tag. Prior: r7's review. The extract now ends at #BC.4-6-1. Q1 lists r7's five findings; Q3–Q5 add c^{VAR}, ε₂^X, ε₃^X, #BC.4-5-3-1-1 and (173)'s ε₂ at the pair. The named steps add #BC.4-1-1-1, #BC.4-5-3-0-1, #BC.4-5-3-1-1 and #BC.5-1-0. allow_defs adds ε₂^X, ε₃^X and ε̄₃. Definition check: 0 conflicts (46 allowed).
- Every changed line was re-read: #BC.3-1-1-2, #BC.4-1-1, #BC.4-1-1-1, #BC.4-1-2, #BC.4-4, #BC.4-5-3-0, #BC.4-5-3-0-1, #BC.4-5-3-1, #BC.4-5-3-1-1, #BC.4-6, #BC.5-1-0, #BC.5-1-3-1-1-1 and #BC.8-5. These uses were grepped: c^{VAR} (#BC.4-1-1, #BC.4-1-1-1, #BC.4-1-2, #BC.4-5-3-0-1, #BC.4-5-3-1-1, #BC.5-1-0), ε₂^X and ε₃^X (#BC.4-5-3-0-1, #BC.4-5-3-1-1), B₅ (#BC.5-1-0, #BC.5-1-1, #BC.5-1-2, #BC.5-1-4, #BC.8), and "ε₂ = B₅ε₁" in BC, TL, the table and BP_LFR2. The table's #T3.27 and VAR p.309 l.13 use it as Proposition 9's conclusion, an upper bound that is consistent with (173).
- Sizes: part 37494 → 37720 characters (the package overrides the 25k limit, per the user). 121 tags. Long lines run 601–634 characters.
- Known weak points: none. A clean round is expected.
- Built at 01:05:06 (table dea9743123b4, labels c4a7a1f9500b, 13 balaban_proofs files frozen, BR fecfa5745a94). Launched at 01:05 as task br9h8kvy9, effort high, one referee.

## Verdict: bp-crit-bc38-20261108-r8 (0 fatal, 0 serious, 2 minor)

Not clean; the clean count stays at zero. Every other step is CORRECT. Both findings are in lines from my repairs. M2's sentence first appears in the r7 repair (it is in neither the r5 nor the r7 snapshot). M1's unfixed C₁ dates from #BC.5's rebuild, but the finding rests on my r7 claim that "Sects. A–E apply to the pair", whose hypotheses (14) and (173) my r8 pre-check did not check.

| # | Finding | Repair |
|---|---|---|
| 1 | #BC.5-1-0: VAR's C₁ of (172)–(173) is not fixed; the pair's base needs (14), so C₁ ≥ 1, and (173)'s inequality needs B₃, C₁ ≥ 1 | #BC.3-1-1-2: B₃ ≥ 1 (#T3.13), as Theorem 1 holds with B₃ and a₁ replaced by any B₃′ ≥ B₃ and a₁B₃/B₃′ (p.279 l.8–13). #BC.5-1-0: C₁ := L³ (p.280 l.20, #T4.6). New #BC.5-1-0-1 checks (14): U₀ ∈ 𝔘(𝐁, B₃ε₁) ⊂ 𝔘(𝐁, C₁B₃ε₁), and |Ū₀^j − V′V₀| = |1 − V′| < C₁ε₁ by (172). It also checks (173)'s inequality and the earlier conditions, and the same holds for 𝐁^X. With B₃ ≥ 1, max{1, B₃} and max{1, 2L²B₃} are removed (#BC.4-1-1, #BC.4-1-2, #BC.4-5-3-0-1) |
| 2 | #BC.4-5-3-1-1: p.281 l.32–34 is VAR's announcement, not the fact used | U_{p,X}(W) lies in 𝔘(𝐁^X, B₃ε₁^X) ⊂ 𝔘(𝐁^X, ε₀^X) and minimises A^X on 𝔙(𝐁^X, W) (#BC.4-1-1; Theorem 1). So #BC.4-5-2-1–#BC.4-5-3-3-2, with it in place of U⌈X, make its image a critical point of 𝔉 on (75)–(77) |

- Pins re-read: VAR p.279 l.6–16, l.40–52, p.280 l.1–32, p.303 l.36–41, p.305 l.28–56.
- Table: the fork entered #T12.27-1 (ε₁^*), #T12.27-1-1 (ε₂^X) and #T12.27-1-2 (C₁ = L³, B₅ = 30dL⁴B₀B₃) as table 565d0ca22a72 (LABELS d4fe87df6146) and re-derived each.
- SHAs: BC d7cb3e924234 → 5a7e144e2669 (BC.2, below) → 034a8d0c7b55. TL is unchanged (#94 cites ε₁^* and #BC.5-1-0 by tag).

## Pre-check: bp-crit-bc38-20261108-r9 (one package, effort high)

- Spec: specs/spec_bc38_r9.json, from r8's spec with BC 034a8d0c7b55 and LF bdc5ce39fb76 (BC cites no LF tag). Prior: r8's review. Q1 lists r8's two findings and asks about B₃ ≥ 1 and the simplified thresholds. Q3 and Q5 are updated. The named steps add #BC.5-1-0-1, and the background adds #T3.13 and #T4.6. Definition check: 0 conflicts (46 allowed).
- Every changed line was re-read: #BC.3-1-1-2, #BC.4-1-1, #BC.4-1-2, #BC.4-5-3-0-1, #BC.4-5-3-1-1, #BC.5-1-0 and #BC.5-1-0-1. These uses were grepped:
  - max{1, B₃} and max{1, 2L²B₃}: none left in BC, TL or the spec;
  - VAR's C₁ (#BC.5-1-0, #BC.5-1-1, #BC.5-1-2, #BC.8-5, #BC.8-5-1, all of which hold for any C₁ ≥ 1);
  - B₅ = 6B₁B₃C₁;
  - the p.305 l.40–44 pin (now only in the table's old r_B text, which the fork replaced).
  #BC.8-2-1's L²B₃ε₁^X ≤ c^X is #BC.4-1-2's 2L⁴B₃²ε₁ ≤ c^X.
- Monotonicity in B₃, for the choice B₃ ≥ 1: (14), (113), (173), Proposition 6's 2B₀C₁B₃ε₁ ≤ 8ε₂ and #BC.4-4-3's α₀ = L²B₃ε₁ are all upper bounds or hypotheses that only weaken as B₃ grows.
- Sizes: part 37720 → 38277 characters, 122 tags. Long lines run 601–634 characters.
- Known weak points: none. A clean round is expected.
- Built at 01:23:18 (table 565d0ca22a72, labels d4fe87df6146). Launched at 01:23 as task bkbhe2shc, effort high, one referee. The user stopped it after asking whether the repairs had been rechecked. It left only a draft stub with no findings.

## Full recheck of the r7 and r8 repairs, before bp-crit-bc38-20261108-r10

r9's pre-check re-read the changed lines and grepped their uses, but did not trace each changed hypothesis through every step that consumes it. That trace is done here.
- **B₃ ≥ 1 (#BC.3-1-1-2).** Theorem 1 (p.279 l.8–28) was re-read in full. With B₃′ ≥ B₃ and a₁′ := a₁B₃/B₃′:
  - B₃′a₁′ = B₃a₁ ≤ a₀, and ε₁ ≤ a₁′ implies ε₁ ≤ a₁;
  - (8): 𝔘(B₃ε₁) ⊂ 𝔘(B₃′ε₁);
  - uniqueness: B₃′ε₁ ≤ ε₀ implies B₃ε₁ ≤ ε₀;
  - (9)–(10) are bounds B₃Mε₁, which weaken;
  - M(ε₁) = R₁M₁(a₁′/ε₁) ≤ R₁M₁(a₁/ε₁) allows fewer M, which also weakens the statement. BC uses neither M(ε₁) nor (9)–(10).
  So every clause of Theorem 1 holds. Each use of B₃ in BC is an upper bound or a hypothesis that weakens as B₃ grows: (13)–(14) with C₁^X (the m^X = 1 check needs C₁^XB₃ > L² and C₁^XB₃ > 2(d − 1)L³, and C₁^XB₃ ≥ 4dL³ gives both), (113), p.296 l.11, Proposition 6's 2B₀C₁B₃ε₁ ≤ 8ε₂, #BC.4-4-3's α₀ = L²B₃ε₁, #BC.8-2-1's B₃ε₁^X, and B₅. The thresholds that contain B₃ are all in ε₁^*, which B₃ ≥ 1 only shrinks.
- **C₁ = L³ (#BC.5-1-0–#BC.5-1-0-1).** Consumers: C₁ε₁ ≤ ½; r_B and r_B^X (≤ L³ε₁/2 ≤ ¼ < log 2); #BC.5-1-1 (|B| < r_B is strict and e^{r_B} < 2, so |e^{iB} − 1| < C₁ε₁, (172) strict); #BC.5-1-2 (2B₅/C₁ = 12B₁B₃); #BC.5-1-4, #BC.5-1-4-1 and #BC.8-1 (r_B^X); #BC.8-5 (2r^{ext}_k < C₁ε₁ for g small); #BC.8-5-1 (2C₁ε₁ ≤ 1 < π). Each holds for any C₁ ≥ 1.
  - (14) at the pair: Theorem 1 at ε₁ needs ε₁ ≤ a₁ (ε₁ < ε₁^*), and |V₀ − V′V₀| = |(1 − V′)V₀| = |1 − V′| because V₀ is unitary and |·| is the operator norm.
  - 𝐁^X: W₀ meets (7) with ε₁^X (#BC.4-4), Theorem 1 holds for 𝐁^X (#BC.4-6), and |B^X| < r_B^X gives (172) (#BC.5-1-4-1).
- **#BC.4-5-3-1-1.** U_{p,X}(W) is a global minimum on 𝔙(𝐁^X, W), hence a local one, and it lies in the open 𝔘(𝐁^X, ε₀^X). These are exactly the inputs that #BC.4-5-2-1–#BC.4-5-3-3-2 use for U⌈X. The argument is not circular: #BC.4-6 depends on #BC.4-5-3-1-1, which depends on #BC.4-1-1 and Theorem 1.
- **Earlier repairs in this cycle.** #BC.4-1-1-1 (c^{VAR}), #BC.4-5-3-0-1, #BC.4-4, #BC.5-1-3-1-1-1, #BC.8-5 and BR's citation in #BC.3-1-1-2: r8 found them CORRECT, and their texts changed since only by the removal of the maxima, which is equal under B₃ ≥ 1. BC.2's Ω_p repair: only BC.2 uses the description (#BC.2-3-2, #BC.2-6); #BC.3-1-1 rests on CRE p.257 l.11–12.
- **Outside BC.** The LF and BP_LFR2 cite only #BC.3-2, which is unchanged. TL #6.16.3-2, #6.16.3-2-1 and #94 were re-read and agree: #94's "ε₁ < ε₁^* and the conditions of #BC.5-1-0", and B₃'s dependence on d, L and G (#BR.15). TL's B₅ is LFR I's (#T1.4), a different constant, and TL's r_B is BC's, a fixed radius chosen before g. The table rows were re-derived by the fork (565d0ca22a72).
- Result: no defect found. The restart is r10, from specs/spec_bc38_r10.json (r9's spec with the revision renamed), BC 034a8d0c7b55, LF bdc5ce39fb76, table 565d0ca22a72. Built at 01:28:11 (labels d4fe87df6146, 13 balaban_proofs files frozen). Launched at 01:28 as task bzwhg583v, effort high, one referee, at the user's instruction.

## Verdict: bp-crit-bc38-20261108-r10 (0 fatal, 0 serious, 4 minor, 1 observation)

Not clean; the clean count stays at zero. Every other step is CORRECT. Findings 1–3 are in lines from my r8 repairs (#BC.5-1-0, #BC.5-1-0-1 and #BC.3-1-1-2's B₃ ≥ 1 clause). Finding 4's pointer dates from the split of #BC.5-1-0 out of #BC.5-1. The observation is in VAR's print (p.280 l.51–52), which #BC.4-5-3-0 reproduced. The full recheck before r10 traced hypotheses into BC's consumers, but not into REG Theorem 2's hypotheses at the base.

| # | Finding | Repair |
|---|---|---|
| 1 | #BC.5-1-0: (1 + 4C₁)ε₁ ≤ a₁ and its ε₁^X form are missing | Added to #BC.5-1-0's smallness. #BC.5-1-0-1 uses it for the pair's ε₀ ≤ B₃a₁ ≤ a₀ (p.279 l.8, p.280 l.42) |
| 2 | #BC.5-1-0-1: the pair's ε₀ is not named | VAR's ε₀ taken to be B₃(1 + 4C₁)ε₁, at which (173) is p.281 l.19's B₁(ε₀ + C₁ε₁). (113), the chart condition ε₀ + C₁ε₁ ≤ c₁, and REG (1.33) with U₀ ∈ 𝔘(B₃ε₁) ⊂ 𝔘(ε₀) are checked there, at (173)'s ε₂ and at Proposition 9's B₅ε₁ |
| 3 | #BC.3-1-1-2: B₃′ ≥ B₃ is justified only for Theorem 1 | New #BC.3-1-1-2-1: in (14) and in (173)'s ε₀, B₃ bounds configurations from above, (113) and p.296 l.8–10 are checked with B₃′, and Proposition 6 holds at B₃′ with VAR's a₄, as (117)'s first term is at most ε₄/2 and the terms 2dLB₀C₁ε₁ of (118) and (121) are at most dLε₄/B₃′ ≤ dLε₄/B₃ (p.295 l.11–20, l.41–45). The block-disjointness sentence moved with it |
| 4 | #BC.8-5-1: "(#BC.5-1)" | Now "(#BC.5-1-0)" |
| obs. | #BC.4-5-3-0: REG (1.33) needs U₀ ∈ 𝔘(α₀), and VAR's α₀ = ε₀ needs C₁B₃ε₁ ≤ ε₀, which (113) does not give. At 𝐁^X with m^X ≥ 2 it is not guaranteed | #BC.4-5-3-0: REG's α₀ is taken to be ε₀ + C₁B₃ε₁, with α₁ = C₁ε₁. (1.33) holds by (14), (1.34) as (18) ⊂ 𝔘(ε₀), and (1.35) by (14). (1.36) and (1.39) give (19) at ε₂ ≥ B₁(α₀ + α₁). #BC.4-5-3-0-1: ε₂^X := B₁(ε₀^X + 2C₁^XB₃ε₁^X). #BC.4-1-1 and #BC.4-1-2: ε₁^*'s third term becomes c^{VAR}/((max{2(d − 1), 2L²B₃} + 4L²C₁^XB₃)B₃). #BC.4-5-3-1-1: 8ε₂^X ≥ 80dLB₀C₁^XB₃ε₁^X |

- Pins re-read: VAR p.278 l.28–48, p.279 l.5–30, p.280 l.33–60, p.281 l.1–30, p.294 l.42–52, p.295 l.1–60, p.296 l.1–14, p.305 l.28–58, p.307 l.1–12, p.309 l.1–16; REG p.082 l.25–60, p.083 l.1–25 (printed line = file line − 1).
- The (7)-constant of V′V₀ is not printed: (173) shows only the ε₀. BC uses no (7) bound for V′V₀ on the whole ball. It uses (173), Proposition 9 (p.309 l.8–16) and p.307 l.4–5 as VAR's results at 𝐁 and 𝐁^X. Near B = 0 it uses (7) at ε₁ by continuity, which gives REG (1.34) at the pair (#BC.5-1-0-1-1, #BC.5-2-1).
- Finding 2's repair is split over #BC.5-1-0-1 (ε₀, (14)), the new #BC.5-1-0-1-1 (REG (1.33)–(1.35)) and the new #BC.5-1-0-2 (ε₂ at (173)'s value and at Proposition 9's B₅ε₁, (113), the chart, a₄, ε̄₃, (103)).
- SHAs: BC 034a8d0c7b55 → a721e71ba8f9. Table 565d0ca22a72 → 0708933874ec (the fork's rows #T12.27-1, #T12.27-1-1, new #T12.27-1-3), now 5ffb7cad1762 (its own rows). TL is unchanged at 6c97421f37d0.

## Recheck of the r10 repairs (three passes, at the user's instruction), and pre-check of bp-crit-bc38-20261108-r11

The user asked for two full rechecks before the next referee. Pass 1 and pass 2 each found defects, so a third pass was run; it found none.
- **Pass 1** (every changed line re-read, every inequality re-derived) found:
  - #BC.3-1-1-2-1 cited p.296 l.11, which BC no longer uses; now l.8–10;
  - "the C₁-terms" is now "the terms 2dLB₀C₁ε₁";
  - #BC.4-5-3-0-1 gained "≥ B₁(ε₀^X + C₁^Xε₁^X)", which (113) needs;
  - #BC.5-1-0-1-1 now labels (1.33), (1.34) and (3.35) explicitly;
  - Proposition 9's pin is p.309 l.13, not l.14;
  - "F₀" was used before #BC.8-1 defines it; now "U_{p,X}(W₀)";
  - three lines were over 600 characters and were split at sentence boundaries.
- **Pass 2** (fresh re-read; (117), (118) and (121) re-derived at B₃′; the uses of the moved sentences grepped) found the ambiguous "is … or Proposition 9's B₅ε₁", now "Proposition 9 takes ε₂ = B₅ε₁".
  - (117)'s first term is B₀C₁B₃′ε₁ ≤ ε₄/2.
  - The terms 2dLB₀C₁ε₁ are at most dLε₄/B₃′ ≤ dLε₄/B₃, so (118) and (121) reduce to VAR's conditions at B₃, and VAR's a₄ holds.
  - Block disjointness is cited by no tag.
- **Pass 3** (all of #BC.5-1–#BC.5-1-1 on the final text, and the fork's rows): no defect.
  - At the pair: 8ε₂ ≥ 32B₁B₃C₁ε₁ = 160dLB₀B₃C₁ε₁ ≥ 2B₀C₁B₃ε₁, ε₃ = 4ε₂ ≥ 4B₁C₁ε₁ > B₁C₁ε₁, and 8B₅ε₁ ≤ 8B₁c^{VAR} ≤ a₄.
  - At 𝐁^X: 8ε₂^X ≥ 16B₁C₁^XB₃ε₁^X, ε₃^X ≥ 8B₁C₁^XB₃ε₁^X, and 2C₁^XB₃ε₁^X = 4L²C₁^XB₃²ε₁.
- **Consumer trace.**
  - ε₁^*: #BC.4, #BC.5-1, #BC.5-2-1 and #BC.8-5 use only ε₁ < ε₁^*, and the smaller third term only strengthens it.
  - ε₂^X and ε₃^X: #BC.4-5-3-0-1 and #BC.4-5-3-1-1 only.
  - "#BC.5-1-0": #BC.5-1-0-2, #BC.8-5, #BC.8-5-1, and TL #94 by tag.
  - B₁ = 5dLB₀ keeps its p.296 l.11 pin (#BC.4-1-1-1).
  - TL, the pair note and BP_LFR2 use no VAR α₀ or (173) (their "(1.33)" is LFR II's). The LF (d0b1ae49772f) cites only #BC.3-2.
  - The table rows are 0708933874ec's, unchanged in 5ffb7cad1762.
- **Spec.** specs/spec_bc38_r11.json, from r10's: BC a721e71ba8f9, LF d0b1ae49772f, prior r10.
  - The claim and Q1, Q3, Q4 and Q5 are updated, and Q1 lists r10's four findings and the observation.
  - The scope adds #BC.3-1-1-2-1, #BC.5-1-0-1-1, #BC.5-1-0-2 and REG p.083.
  - Definition check: 0 conflicts (46 allowed).
- Sizes: part 38277 → 39614 characters, 125 tags. The long lines run 601–634, as before.
- Banned words: none. Known weak points: none. A clean round is expected.
- Built at 01:56:47 (table 5ffb7cad1762, labels 88868d1c3cce, argument 51817 characters). Launched at 01:56 as task badtj1r3c, effort high, one referee. The user stopped it at 01:59 and asked for a full recheck of everything before any referee. The first item found then: #BC.4-1-1-1's ε̄₃ omits p.293 l.46–48's stronger restriction for Proposition 4 at 3ε₃.

## Full hypothesis recheck of #BC.3–#BC.8-5-2, before any further referee

Method: for every result that BC applies, its printed hypotheses are quoted from the transcription and checked at each application, at 𝐁 and at 𝐁^X; every inequality is re-derived. The findings and their repairs are listed per step below.

- #BC.3: correct (VAR p.277 l.11–17; RG I (0.4), (0.12) and p.252 l.27–32).
- #BC.4: correct apart from defect 1 (VAR p.278 (2)–(7), p.279 l.8–28, p.280–p.281, p.285–p.296; REG (1.1)–(1.2), (1.33)–(1.39), p.080, p.088 l.36; CMP98 (52)–(54), (105)–(106)).
- #BC.5-1–#BC.5-1-3-1-3: correct (CMP98 p.020 l.17–31, p.024 l.22–29, p.024 l.52–p.025 l.7; VAR (17), (172)–(173); REG (1.18); BD Step 6).
- #BC.5-1-3-2: correct. CMP98 (69) is p.029 l.29–31, (97) is p.032 l.28–35 with R̄^j_{0,b} acting by conjugation as in (55), (59) is p.027 l.35, and (105) is p.033 l.38–40; v_j has the factors 0 to j − 1.
- #BC.5-1-3-3–#BC.5-1-3-4: correct. The cube of side 3L^{j+1}η about x lies within 3L^nη of z, Proposition 2 is applied at α₀ = L²B₃ε₁L^{2(j−n)}, and (S2) is applied with 2dL𝔞_j ≤ 4d√NLt(B) ≤ ε and 80A_dL²B₃ε₁ ≤ ε (from c^X). Σ_{j<n}L^{j−n} < 1/(L − 1), and e^x − 1 ≤ 2x for x ≤ 1.
- #BC.5-1-3-4-1–#BC.5-1-3-4-2: correct apart from defect 2. RG I p.253 l.14–16 is the analyticity of M on G^c. The bound |ψ(a, −b) − b| ≤ 2|a| follows from |∂_aψ − I| ≤ 1 and ψ(0, −b) = b. Step 3's domain is used at ρ = 2ρ₀.
- #BC.5-1-4–#BC.5-3-1: correct apart from defect 3. VAR Proposition 9 is p.309 l.8–14, with ε₂ = B₅ε₁ at l.13. p.307 l.1–5 is the axial continuation, and (19) is p.281 l.5–10. REG (1.17) is p.078 l.44–48 and (1.18) is l.50–54. VAR p.278 l.15 and p.280 l.45 give gauge invariance, and (7) is p.278 l.35–37.
- #BC.6–#BC.7-2-1: correct. REG p.076 l.31–47 is (1.1)–(1.2), p.077 l.48–52 is (1.11), and CMP98 (56) is p.027 l.11. RG I p.261 l.40 is π and p.278 l.47–52 is (3.42). CRE (2.34)–(2.37) is p.261 l.13–24, and the case n = m is CRE's X ∩ Ω_m, since X ⊂ Ω_{m+1}^c (#BC.1-5).
- #BC.8–#BC.8-4-1-1: correct apart from defect 4. CMP98 (87) is p.031 l.16–18, and the uniqueness statement is at l.20. The cube for (S2) at x_{l+1} lies within 3L^nη of y, hence in Ω^X_{n−1}, as R′M′ ≥ 3dL. Θ ≤ e^{24d√Nt^X + d(t(B) + t^X)}.
- #BC.8-5–#BC.8-5-2: defect 5.

| # | Defect | Repair |
|---|---|---|
| 1 | #BC.4-1-1-1: ε̄₃ omitted the estimates at 3ε₃ (VAR p.293 l.46–48) | They are added to the conditions fixing ε̄₃, with #T3.32-1 and #T3.32-2 cited |
| 2 | #BC.5-1-3-4-1-1: ρ₀ ≤ c_γρ₀ used c_γ ≥ 1 without citation | c_γ = 3d(d + 1) (#BD.10-1, #BD.6-3). The line is split at its sentence boundary into #BC.5-1-3-4-1-1 and #BC.5-1-3-4-1-2 (it was 657 characters) |
| 3 | #BC.1-4-2 and #BC.5-1-1: Proposition 9 was pinned at p.309 l.8–16, which includes the references heading | Now p.309 l.8–14 |
| 4 | #BC.8-4-1: "𝔤^c-valued there" read as at 𝔤-valued B | Now "on that ball and on 𝒱". G^c's definition moved to #BC.5-1, its first use, so that it is stated once |
| 5 | #BC.8-5: B was taken to be 𝔤^c-valued because V′ is G^c-valued and near 1, which does not follow for an arbitrary subgroup generated by e^{i𝔤^c} | D2.7 15.6(d) and TL #167 give V = e^{iε^{dev}} and V₀ = e^{iε^{dev}_0}, with ε^{dev}_0 𝔤-valued and |ε^{dev} − ε^{dev}_0| < 2r^{ext}_k. Duhamel's formula and the Lie product formula then give |V′ − 1| ≤ 4r^{ext}_k, so |B| ≤ 8r^{ext}_k, and B is 𝔤^c-valued by the identity theorem in ε^{dev}. New #BC.8-5-1-1 is split off at a sentence boundary. The deviations are named ε^{dev}, since BR's ε is a constant of BC |

- BC: a721e71ba8f9 → bd791c479a27, 52828 characters. The longest new line is #BC.8-4-1 at 580 characters; the lines over 600 are the earlier ones, at 601–634.
- Recheck pass 1: each repaired line was re-read in full, and every inequality and pin re-derived: e^{2r} − 1 ≤ 4r for 2r ≤ 1, |log(1 + Z)| ≤ 2|Z| for |Z| ≤ ½, 8r^{ext}_k < r_B for g small, and c_γ = dc_β with c_β = 3(1 + d). No defect.
- Recheck pass 2 (consumers): ε̄₃ is used in #BC.4-5-3-0, #BC.4-5-3-0-1 and #BC.5-1-0-2, which use only its definition. (103)'s lower bound on ε₃ is checked at 𝐁 (#BC.5-1-0-2) and at 𝐁^X (#BC.4-5-3-1-1). No line in BC, TL or the table used the old |B| ≤ 4r^{ext}_k. TL #6.16.3-2 cites #BC.5–#BC.7 and TL #6.16.3-2-1 cites #BC.8-5-2, and neither changed. The ranges #BC.5-1-3-4-1–#BC.5-1-3-4-2 and #BC.8-5–#BC.8-5-2 contain the new tags. No defect.
- Table rows for the fork: #T12.27-1-1's ε̄₃ text needs p.293 l.46–48 and #T3.32-1 for a₄; #T12.27-1-2's G^c needs the citation #BC.5-1; #T12.27-6's V′ needs the citation #BC.8-5-1; and ε^{dev}, ε^{dev}_0 (#BC.8-5) need entries. The fork entered them at table 7e04c266ddd5: #T12.27-1-1 (its ε₂^X sentence moved to #T12.27-1-1-1), #T12.27-1-2, #T12.27-6 and the new #T12.27-6-1. All four were re-read against BC and match it. The fork's split of #T4.56 is not cited by any of my files.

## Pre-check of bp-crit-bc38-20261108-r12

- Spec spec_bc38_r12.json, made from r11's: rev r12, LF 07065b0520af, prior r10's review (r11 was stopped and has no review), BC bd791c479a27. The claim names the five repairs, Q1 asks whether they are correct, and Q5, Q7 and Q8 point to #BC.5-1-3-4-1-2, #BC.5-1 and #BC.8-5-1–#BC.8-5-1-1. The scope lists the new tags, and the caller now states what #BC.8-5 takes from TL #167 and D2.7 15.6(d). allow_defs for B and V′ point to #BC.8-5-1. The JSON is valid, and --check finds 0 conflicts (46 allowed).
- Every changed line was re-read twice (the recheck passes above), and every use of ε̄₃, c_γ, G^c, V′, B and the new ε^{dev}, ε^{dev}_0 was grepped in BC, TL, the pair note and the table. Restated facts: G^c is now stated once, in #BC.5-1. Size: 52828 characters for BC in all; the package grows by the Duhamel step only.
- Banned words: none. Known weak points: none. Open items being worked on: none.
- Built at 02:34:54 (LF c6924224635c, which the LF session changed during the pre-check; table 7e04c266ddd5; snapshot BC bd791c479a27; argument 52544 characters (58351 bytes), against r11's 51817: +59 in #BC.3–#BC.4-6-1 and +668 in #BC.5–#BC.8-5-2, from the ε̄₃ clause, the c_γ citation and #BC.8-5-1's Duhamel step; reviewed blocks 40345 characters). Launched at 02:35 as task bi2obaspk, effort high, one referee.
- Size history of the reviewed blocks #BC.3–#BC.8-5-2 (characters): r1 18277, r2 21968, r5 30136 (after the bc38a and bc38b parts were merged), r7 36148, r8 37732, r10 38287, r11 39618, r12 40345. By section, from r1 to r12: #BC.3 3.3k to 5.2k, #BC.4 5.0k to 13.5k, #BC.5 5.1k to 12.7k, #BC.6–#BC.7 2.5k to 3.0k, and #BC.8 2.3k to 6.0k. Most of the growth is in hypothesis checks added one finding at a time, with the same threshold checks made separately for 𝐁, for 𝐁^X and for §G's pair (#BC.4-1-1–#BC.4-1-2, #BC.4-5-3-0–#BC.4-5-3-1-1, #BC.5-1-0–#BC.5-1-0-2). To be condensed after r12's report.
- During r12, context lines only (#BC.1 and #BC.2, not under review): VAR p.277 l.16–17 is now l.17 (l.16 is the end of (1)); CRE (2.11) p.256 l.35–39 is now l.36–41; (2.12) p.256 l.41–51 is now l.43–51; LFR I p.190 l.17 is now l.18, the line of U_{p,X}.

## Pre-read: BP_LFR2_REPLACEMENT.md, before its first round

Read in full during r7; the file is not under r7's review (it is frozen in r7's snapshot). Pins re-read: LFR II p.356 l.31–37, p.365 l.2–41, p.370 l.3–5; LFR I p.195 l.5–8, p.197 l.21–43; VAR p.278 l.2–47, p.279 l.1–15, p.301 l.44–45, p.305 l.31–47, p.308 l.37–47 (190), p.309 l.8–14; CMP98 p.019 l.12–14, p.026 l.46–52; CRE p.255 l.15–16, p.256 l.58–62, p.264 l.52, p.269 l.9; REG p.075 l.8–9, p.078 l.14–18, p.088 (1.70)–(1.72), p.089 l.35; RG I p.253 (0.4), p.254 l.2–6.

| # | Defect | Repair |
|---|---|---|
| 1 | #160.2: the frame of V_k′, V_Λ, V″ is left open (U is only a gauge transform of U_k by #134) | U = U_k^u, V = V_B^u, and (V_k′V_Λ)^u(b) = [u(b₋)V_k′(b)u(b₋)^{−1}]V_Λ^u(b). So the transforms are written again V_k′, V_Λ, V″, B′ keeps its norm (#T11.35), and the whole construction uses these data (new #160.2-0, split off at a sentence boundary) |
| 2 | #160.2-1: κ_s clashes with the two-loops note's κ_s | κ_s^{LF} = 1/240 (#T3.34-1), which also gives the factor 2 used in #160.3-2 |
| 3 | #160.4-3: VAR's uniqueness needs B₃ε₁ ≤ ε₀ ≤ a₀ (p.279 l.15), which was not checked; Theorem 1 at ε₁ = O(ε₀^♭) would need M ≥ M(ε₁), which grows as ε₁ → 0 | The data satisfy (7) at ε₁^♭ = O(ε₀^♭) (new #D.ε₁^♭) ≤ ε₁, #160.3's fixed admissible value (#T3.20). Uniqueness is applied in (6) at B₃ε₁, with ε₀^♭ ≤ B₃ε₁ ≤ B₃a₁ ≤ a₀ (#T3.29, #T3.31) |
| 4 | #160.4-2: the neighbourhood sentence mixed up the Z-problem's space and the global one | U^♭ minimises on the global (8) at V^♭, which is defined by the strict bounds (2), so the configurations equal to U^♭ off Z, close to it on Z and with 𝔹_k(Z)'s data lie in (8) (VAR p.301 l.44–45) |
| 5 | #160.4-1: REG p.75 l.9 only mentions compositions of averages | The pin is now RG I (0.4), (0.12) (p.253, p.254 l.2–6) and #BC.3-2. The LF session was told, since LF #3.85.1 has the same pin |
| 6 | #160.7-1: the bound on u^♭ used the global sup of 𝐇^♭, which is not small | It now uses sup over B^k(y), because REG (1.70)–(1.71) bound the transformation at y by averages over the blocks B(x_{n+1}) ⊂ B^k(y), where #160.7's decay applies |
| 7 | #160.7: the step from 8MR_k to 7MR_k was not shown | 8MR_k − 2M₁ − 1 ≥ 7MR_k, as M₁ < M and R_k ≥ L ≥ 2 (#T2.23) |

- SHA 525a536d7b52 → 700d2a04d167; 8951 characters, under 25k. The header line is 618 characters long. The table fork was asked to enter ε₁^♭ and the frame convention in the row at table line 446.
- These were re-read against the steps that use them, with no further defect: TL #41.1 (the frame identity of #160.8), #43 (#160.8-2), #105–#106 (#160.3-1, #160.7-1), #134 (#160.2), #161 and #5.3, #5.6 (#160.8-1); LF #3.86–#3.86-1 (#160.6-2), #3.96-1-1 (#160.2-1), #4.44-0 and #4.48-3.0.1 (#160.7). The user is TL #45 and #160. It needs δ^{re} on Λ ∩ Ω″^{∼2}_{h+1} per block of 𝐁_k″(Y₁) at the real base, with the data agreeing off Λ, and #160.1 gives exactly that.
- The table fork entered ε₁^♭ as #T12.18-1 and the frame convention (table a1fc86e0650f, LABELS f2964f4e9849, then cf1721e09609 at LF 6e38d5fd2a97 after the LF session's #3.85.1 pin repair).

## Pre-read: BC.2 r4 (#BC.1–#BC.2-6-1), during bc38 r7

- Re-read and correct: #BC.2-1-3 (M ≥ L²M₁), #BC.2-4-2 (strict separation 2dM₁L^qη < M₁L^{q+1}η), #BC.2-5-3–#BC.2-5-4 (the inner, outer and bond conventions are carried consistently: in the inner case a_f ∈ X, in the outer a_{f−1} ∈ X, and a bond lies in X through a_{f−1}), and #BC.2-6 (a)–(c).
- Settled (read CRE p.256 l.35–63, p.257 l.1–30, p.261 l.1–70, LFR I p.189 l.38–p.190 l.40, LFR II p.373 l.17–29). In "𝐁_p(X) ∪ {Γ_i}_{i<p}" (CRE p.261 l.10; LFR I p.190 l.14–17, p = 1, …, k), as in LFR II's "𝐁(Y₁) ∪ 𝐁_k″", the localised set comes first and the global set second. Every point of 𝐁^X is a point of one of the two, and {Γ_i}_{i<p} has no points in Ω_p. So 𝐁^X's points in Ω_p are points of 𝐁_p(X), with indices ≤ p, which agrees with U_{p,X}'s step-p units L^{−p} in (2.35) and (2.37). #BC.2-3-1 had "the points of 𝐁 in X∖S^q_X", which is false inside Ω_p, where 𝐁_k's indices go up to k. It now describes 𝐁^X outside Ω_p, through {Γ_i}_{i<p} and 𝐁_q(X). #BC.2-3-1-1 (*Inside Ω_p*) derives the points in Ω_p, and #BC.2-3-2 (a)–(c) now agree with both. Only BC.2 used the old description: #BC.3-1-1 takes VAR's conditions for 𝐁^X from CRE p.257 l.11–12 and #T2.15. BC d7cb3e924234 → 5a7e144e2669, after r8's snapshot (BC.2 is context there, not under review). BC.2 r4 sees it. BP_LFR2_REPLACEMENT.md is ready for its first round once bc38's clean count is done and BC.2 r4 has run.

## TL symbol clashes (the table fork's list)

- win_𝒞, win_M: TL's window has four ends (two loops), each reaching 20(diam_v + 1) (map #MD2.4.12.31), so its 80 is correct and is a different quantity from the map's 40. Renamed |win^{(2)}_𝒞| (#543) and |win^{(2)}_M| (#576), with the relation stated in #539. Table #T12.2-12 mirrors it.
- λ in #41.2: local λ := (1/i)log g, renamed λ_g. The other λ's of TL are #T4.30's.
- The table fork named the collisions, and each was renamed to a symbol free in TL and the table: P := H′Q′ of #5.10.1–#5.10.3 → P_H; R₀ := 𝓗(δ^{re}) (#161) → 𝓗^{re}; c_F (#636) → c_F^×; C^R (#662) → C^×_{KP}; θ(G) (#250) → θ^×(G); w̄ (#894) → w̄^×; c_p (#88.1-4) → c_p^×; σ_n (#88.1-3-0) → σ^s_n.
- hull(g): TL's cross-group set ∪_{P∈g}dom P, smaller than D2.7's span(g) ∪ ∪dom P, is now hull^×(g) at #518–#521, #678–#684, #717, #721 and #795; D2.7's hull(g) stays at the single-loop and D2.7 uses.
- c_π (#169) is the large-field note's ‖dπ‖ (LF #D.‖dπ‖), now stated so, and distinguished from #T4.2's PBG constant.
- TL 58345871948f → 5cec29cb2bba → b5b13afa28dc → 71875046f97b. The table fork was sent every new symbol and mirrored them (table b731a0e86fc1).
- Pair note: #PC5.2-5's C^R (TL #662's constant) → C^×_{KP}, and w̄ → w̄^× at #PC4.2-2.1, #PC4.11.1, #PC4.13-4, #PC4.14-3.5, #PC4.14-3a.3 and #PC4.14-5.3; pair note 441d64a649ad → c268cb626c5d.

## Derived, awaiting review: CRE (3.43)'s A-radius C₁p₁(g_k)

- **Closure (22:45).** The domain was already derived: the O6 closure §3 and §5 (map #MD2.2.6.170-3) prove that the localised terms with analyticity space (3.43) are analytic in (A_k, A) jointly on 𝒫_k^{3/4} = {sup|B′| < 3r_{α,k}/4}, with r_{α,k} = min(β,1)α_{1,k}/(16B₀e^{16κ_s}) and |B′| ≤ C₁^{RG2}g_k sup|B|. The bounds there: the 𝐏^{(k)}-terms have their printed bounds with the fluctuation factor at most doubled, and the bracket terms (𝐁_k, 𝐄_k, 𝐑_k″) have the Schwarz bound M_Y^{loc}·4sup|B′|/(3r_{α,k}), coefficient O(ε_k/α_{1,k}); p.277's O(ε_k) is recovered at the consumers' points (§5a). §7 records that (3.43)'s A-domain is not used. TL #167-1 now defines r^{an}_k := 3r_{α,k}/(4C₁^{RG2}), and #167-2 computes r^{an}_k = 3min(β,1)λ_Rα_{0,k}/(64B₀e^{16κ_s}C₁^{RG2}), a constant times α_{0,k}. (The first version, at 22:45, used 𝒫_k^m and the doubled factor for all terms; O6 §5, re-read in full, corrected both.) The LF session's check found that points within 2r^{ext}_k of a real datum (g_k sup|B| ≤ ε_k^♯, O6 §4) could leave 𝒫_k^{3/4}. Re-derived and adopted: r^{ext}_k := min(r^{an}_k/8, c_{ext}α_{0,k}), with (C3) giving ε_k^♯ < 2r^{an}_k/3, so the points have g_k sup|B| < (11/12)r^{an}_k. #167-2 also states that (iv) uses only (2.42)-type sup bounds for the B-terms (#153, #6.17.2), which O6 §5's M_Y^{loc} gives with the factor 2c_σ and the rate κ′.
- **Using the radius in CRE itself.** CRE uses (3.43) only at p.276 l.30 and l.46; after that the fluctuation field is integrated over its support, |g_kA| < δ_k. 𝒫_k^{3/4} contains the support under O6's (C3) (q₁ > p₀ and g small, or the constant condition at q₁ = p₀). The ball |A| < C₁p₁(g_k) with LFR I's p₁ < p₀ does not. The later steps need no more than this. The Sect. 7 [I] cluster expansion (CRE p.277 l.24–p.278 l.45; (I.7.x) = RG II (2.x)) integrates over real A in the support and bounds the activities by |𝐕_k(Y, A)| at those points (RG II (2.15), p.15 l.23–37). Its Cauchy estimates are in τ(Y) and σ(Z), with complex parameters and analyticity in (𝐔, 𝐉) (p.15 l.2–6, l.23), and none is in A. At the support, O6 §5a gives p.277's O(ε_k). So 𝒫_k^{3/4} can replace (3.43)'s A-ball in CRE under (C3). The OPEN is deleted, and #167's heading says derived, not reviewed. TL #6.17.2's pin is now "derived from CRE p.277's margin (map #MD2.2.6.170-3)". TL b4d3df110579. The LF session (D2.7 15.7, map #MD2.4.11.15-2, #MOMGD.3-17) and the table fork (#T4.50) were told. The O6 closure was reviewed in round 46 and its serious findings repaired; it has not been re-reviewed.

## Rework of #BC.3–#BC.8 after r12 was stopped

- **r12.** The user stopped r12 (task bi2obaspk) at about 02:40, before it reported. The reason was the packet's size: the reviewed blocks had grown from 18.3k characters (r1) to 40.3k (r12) because repairs kept adding layers of threshold checks. r12 has no review, and the clean count is still at zero.
- **What was deleted.** These lines re-derived the constants of VAR's proof of Theorem 1 and of §G. They now cite VAR Theorem 1 and Proposition 9 in VAR's own setting, accepted as printed:
  - #BC.4-1-1-1 (c^{VAR}, ε̄₃);
  - C₁^X and the c^{VAR} terms of ε₁^* and #BC.4-1-2;
  - #BC.4-5-3–#BC.4-5-3-1-1 (U₀^X's (14), REG Theorem 2's α₀ and α₁, ε₂^X, ε₃^X, and the conditions of Propositions 5 and 6);
  - #BC.5-1-0-1, #BC.5-1-0-1-1 and #BC.5-1-0-2;
  - #BC.3-1-1-2-1 and the B₃′ device, used only by the deleted lines;
  - the SU(2) remark #BC.8-4-1-1.
  Accepting these results is not a weakening. VAR Theorem 1 holds for every sequence meeting the standing conditions, with W satisfying (7) at ε₁^X ≤ a₁ and B₃ε₁^X ≤ ε₀^X ≤ a₀ (#BC.4-1-2, #BC.4-4). §G and Proposition 9 hold "for ε₁ sufficiently small" (p.305 l.35), which is now the constant ε₁^G of #BC.4-1-1. r10's observation that REG (1.33) needs α₀ ≥ ε₀ + C₁B₃ε₁ is about the constants inside VAR's proof; it does not refute the theorem, and is absorbed in a₀.
- **What was kept, rewritten in place.** The one argument outside VAR's setting is that U⌈X, a local minimum on (6), is critical in VAR's chart. #BC.4-5-3–#BC.4-5-3-3 make that argument in four lines, down from eleven: A′_X is the solution of (59) with (62) (p.287 l.9–31), the real line in (75)–(77), reality, Y_s, the local minimum, and ℂ-linearity.
  #BC.4-6 now uses only what VAR's proof states: exactly one critical A′, that of the minimal orbit (p.281 l.21–33, p.290 l.6–8), and the one-to-one map of Proposition 2 (p.281 l.21). The orbit sentence moved to #BC.4-6-1.
  ε₁^* := min{a₁/max{2(d − 1), 2L²B₃}, c^X/(L²B₃max{1, 2L²B₃}), ε₁^G/max{1, 2L²B₃}}. The middle term replaces c^X/(2L⁴B₃²), which gave L²B₃max{ε₁, ε₁^X} ≤ c^X only when 2L²B₃ ≥ 1. #BC.5-1-0 is now C₁ = L³ and r_B, r_B^X.
- **Condensed with no change to the mathematics.**
  - #BC.5-1-3-1–#BC.5-1-3-1-1-1 became two lines (CMP98's axial-gauge bound and the box argument).
  - #BC.5-2-1–#BC.5-2-2 were tightened.
  - #BC.5-3-1's intermediate identity was dropped.
  - #BC.8-2-1's thresholds now read B₃ε₁^X ≤ c^X.
  - #BC.8-5 no longer cites the conditions of #BC.5-1-0.
  - TL #94 now cites only ε₁^* of #BC.4-1-1 (TL 14bce2a70216).
- **Size.** Before: 40252 characters, with lines over 600 characters at 69 (634), 70 (609), 107 (601), 108 (626), 110 (633) and 121 (620). After: 33.9k characters, with #BC.3–#BC.4 at 14.6k and #BC.5–#BC.8 at 19.2k. One line is at 605, #BC.4-5-3, and no other line is over 600. The workflow's limit is 25k characters per packet, so the next round is split at the proposition boundary into bc38a (#BC.3–#BC.4) and bc38b (#BC.5–#BC.8), each with the other part supplied as context.
- **Recheck, pass 1.** Every changed line was re-read, and every new pin was checked against the transcript: p.279 l.8–15, p.281 l.1–33, p.287 l.9–31, p.289 l.26–57, p.290 l.1–8 and l.28–47, p.305 l.30–44, p.309 l.7–14, and CMP98 p.024 l.22–29, l.50–p.025 l.7.
  Pass 1 found one defect: #BC.4-5-3 no longer named the fixed point of (61), and VAR's symbol X for it clashed with the region X. The text now says "H of the fixed point of (61)" in #BC.4-5-3 and #BC.4-5-3-1.
  The greps came back clean:
  - no tag cited in BC, TL, the pair note or the LF is undefined;
  - none of the deleted symbols remains in BC or TL;
  - no banned word is present.
  ε₁^G has no clash in the table or in balaban_proofs/.
- **Recheck, pass 2.** The criticality chain was re-derived from VAR's text. Proposition 2 maps each orbit to a unique axial representative and then to U₁ one-to-one, and (47) is a function. So A′_X = A′_min gives A_X = A_min, which gives the same orbit; only (59)'s solution with (62) is used, not injectivity of (47).
  The thresholds were re-derived:
  - ε₁^X ≤ a₁;
  - B₃ε₁ and B₃ε₁^X ≤ ε₀^X ≤ B₃a₁ ≤ a₀;
  - L²B₃max{ε₁, ε₁^X} ≤ c^X, which gives #BC.4-4-3, #BC.5-1-3-1-1, #BC.5-1-3-3-1 and #BC.8-2-1;
  - C₁ε₁ and C₁ε₁^X ≤ 1, which gives r_B, r_B^X ≤ log 2.
  Pass 2 found one defect: ε₁^G must serve 𝐁 and 𝐁^X alike, and #BC.4-1-1 now says so, citing #BC.3-1-1-2. There was no further defect. BC is 12fcb3b7f8ba.
- **Table.** At 02:52 the table fork was told which rows to change: #T12.27-1 (the new ε₁^*, ε₁^G, and dropping "B₃ ≥ 1"); deletion of #T12.27-1-1 and #T12.27-1-1-1; #T12.27-1-2 (U₀^X cites #BC.4-5-3, and the SU(2) clause goes); and #T12.27-1-3 (#BC.5-1-0 only). The new SHA is awaited.

## Verdict: bp-crit-bc38a-20261108-r13 (0 fatal, 0 serious, 4 minor)
Part a (#BC.3–#BC.4-6-1) is mathematically correct, with four minor findings on clarity and citations. The round is not clean, so part a's clean count stays at 0.

## Repairs (bc38a r13)
| Finding | Repair |
|---|---|
| #BC.4-3: VAR (2) at bonds of Ω^X_0∖Ω^X_1 whose REG (1.2) terms leave X̂ was read without saying so, and the subset reading misses half-defined terms | The statement now gives the convention: (2) bounds every partial sum of the 2(d − 1) summands of #BC.4-3-2 defined on X̂, an open condition. #BC.4-3-2 bounds each summand by B₃ε₁η^{−1} and any sum by 2(d − 1)B₃ε₁η^{−1} ≤ ε₀^Xη^{−1}. #BC.4-5-2-1 covers gauge invariance of the partial sums, since each summand is multiplied by R(u(x)) |
| #BC.4-5-3: "hence in (75)–(77)" compressed three implications | The new #BC.4-5-3-1 (*The line*) gives them: (75) by (20) and (48), (76) by (21) and RD*HB = 0 of (45), and (77) by (62), as 2ε₂ ≤ ½ε₃ (VAR p.281 l.12–17, p.285 l.21–24, l.38–42, p.287 l.27). The reality and Y_s lines are renumbered -3-2 and -3-3 |
| #BC.4-5-3-3: the converse REG (1.31) ⇒ data W was used unstated, and the (1.30)/(1.31) pins were mixed | The new #BC.4-5-3-4 and -3-4-1 state the converse. With u = u(U₁) of CMP98 (87), (97), (99) and (105), the left side of (1.30) is Ū̄₁^j inside Λ_j (CMP98 (92)), and at a crossing bond it is the average (105) of R̄^{j−1}Ū̄₁^{j−1} over contours in Λ_{j−1} times (Ū̄₁^j)_b (REG p.081 l.33–p.082 l.2). These are identities in U₁, so (1.31) at level j, with its first line at level j − 1, gives (1.30), pinned at REG p.081 l.23–29 |
| #BC.4-6: uniqueness was pinned at the reduction p.290 l.6–8 | It now also cites Propositions 5 and 6 (VAR p.294 l.33–40, p.295 l.47–49) |

## Recheck of the r13 repairs and pre-check of bp-crit-bc38b-20261108-r13 (full round of part b, effort high)
- **Pass 1.** Each repair was checked against the corrected transcriptions:
  - VAR p.281 l.1–33, p.285 l.18–43, p.287 l.8–31, p.289 l.42–58, p.290 l.1–10 and l.32, p.294 l.30–42, p.295 l.44–51;
  - REG p.081 l.21–44 and p.082 l.1–18 (printed = file − 1).
  - The pins are correct. Two rewordings followed: in #BC.4-5-3-4, the crossing-bond product is now written in REG's order (average times (Ū̄₁^j)_b) and the levels used are stated, since only (1.31)'s first line at j − 1 enters; and #BC.4-6's Proposition 5 pin is now l.33–40.
  - ε₀^X ≥ 2(d − 1)B₃ε₁ by #BC.4-1-2, which the partial-sum bound needs.
- **Pass 2 (narrower than pass 1; corrected at 12:09).**
  - The r13 repair lines (#BC.4-3–#BC.4-3-2, #BC.4-5-2-1, #BC.4-5-3–#BC.4-6) had one full recheck before the launch, pass 1. #BC.4-5-3-4–#BC.4-6 were re-read after the last edits only at 12:09, after the launch. The second recheck pass of the repairs is still owed, before bc38a r14.
  - #BC.3–#BC.3-5 and part b (#BC.5–#BC.8-5-2) were re-read in full.
  - Every bound in part b was recomputed: r_B ≤ log 2, the Schwarz bound, the axial-gauge box, the BD and (S2) conditions, C_{BX} = 4(6d + 2)√N, the sums over j < n and l < n, the path length, and Θ's exponent. Each matches its threshold in c^X or #BC.5-1-4.
  - Part b's citations of VAR, CMP98, REG, RG I and BR were not re-checked against the transcriptions before the launch. Of BD's, only c_γ = 3d(d + 1) and c_γρ₀ ≤ r_ψ were checked (#BD.10-1, #BD.13), at 12:09.
  - No defect was found.
- **After the launch (12:12), while bc38b r13 runs.**
  - Every citation in part b was checked against its transcription:
    - VAR p.280 l.20, l.34–37, l.45; p.281 l.1–10; p.305 l.31–44; p.307 l.2–5; p.309 l.8–14;
    - CMP98 p.020 l.17, l.30–35; p.024 l.22–29, l.52–p.025 l.7; p.027 l.2, l.11, l.35; p.029 l.29–31; p.031 l.20 and (89)–(92); p.032 l.28–35; p.033 l.39–46;
    - REG p.076 l.31–47, p.077 l.48–52, p.078 l.44–54, p.088 l.36;
    - RG I p.253 l.14–20, p.261 l.36–40, p.278 l.47–52;
    - CRE p.261 l.5–24, (2.34)–(2.37) for X ∈ 𝐃_j, so that m = j in #BC.6-1;
    - BR #BR.1-1, #BR.2-0, #BR.2-1, #BR.2-4, #BR.4-1, #BR.5, #BR.5-2–#BR.5-5, #BR.11-1;
    - BD #BD.2, #BD.3-2, #BD.3-3, #BD.9, #BD.9-1, #BD.11-2, #BD.11-3, #BD.12;
    - TL #94, #94-1, #167, #167-3, #167-4, #6.16.1-1, #6.16.3-2, #6.16.4-2.
    Each is quoted correctly and used within its scope. No defect was found.
  - The second recheck pass of the r13 repairs in part a was made. #BC.4-3–#BC.4-3-2, #BC.4-5-2-1, #BC.4-5-3–#BC.4-6 were re-read after the last edits. (83) is QδA′ = 0, RD*δA′ = 0 (VAR p.290 l.44–47), so along the line (75) holds with B fixed and (76) holds for all s. (82) is ℂ-linear in δA′, the second slot of ⟨·,·⟩. No defect was found.
- **Tags.** All BC tags cited inside BC resolve. The table cited #BC.5-1-3-1-1-1, which the rework had deleted; the fork re-pointed it to #BC.5-1-3-1-1 (table d5d171579d1e). Of the renumbered tags (#BC.4-5-3-x), the table cites only #BC.4-5-3 and #BC.4-6, both still correct.
- **Fork's G^c point.** BC uses CMP98's G = e^{i𝔤} (p.020 l.30), so G is connected and lies in the subgroup generated by e^{i𝔤^c}. No change is needed, and the fork was told.
- **Sizes.** Part a is 15.5k characters and part b 19.3k. Every line is at most 600 characters, measured in characters with Python; #BC.4-5-3-4 was split.
- **Spec b.** It uses BC c1e9157106d9 and LF a51211571c45. The conditional sentence on the stale rows was dropped, since #T12.27-1-0 and -1-3 now match BC. The check gave 0 conflicts with 31 allowed.

## Verdict: bp-crit-bc38b-20261108-r13 (0 fatal, 0 serious, 8 minor)
Part b (#BC.5–#BC.8-5-2) is mathematically correct, with eight minor findings on applicability, wording and citations. The round is not clean, so part b's clean count stays at 0.

## Repairs (bc38b r13)
| Finding | Repair |
|---|---|
| #BC.5-1-3-3: the coverage of the j-bonds of B^{j+1}(x) by the region of #BC.5-1-3-1 was not shown | Each such b has S_b in the cube of side L^{j+1}η centred at x, within ℓ∞-distance (1 + ½)L^nη of z (#BC.5-1-3-1-3). The plaquette bound moved to the new #BC.5-1-3-3-0 |
| #BC.8-5: "at every datum" versus the caller's "per scale-k bond" | #BC.8-5 now reads ε^{dev} 𝔤^c-valued, with the operator-norm bound at every datum of 𝐁_k. TL #167 and #167-3 now read "at every datum of 𝐁_k", and #167-3 takes the maximum over the data of 𝐁_k as its norm. Re-derivation: each datum of a Cauchy point is within t + max deviation, which is less than 2r^{ext}_k, so the narrower domain still contains the points. The LF session was sent D2.7 15.6(d)'s wording |
| #BC.8-5-2: the representative of U_{p,X} at complex data was not named | #BC.8-5-2 now says that U_{p,X}(M^·(𝐔)), the TL's U^d of #6.16.3-2, is F(V), the analytic continuation of #BC.1-4-2 for 𝐁^X about W₀ (#BC.5-1-4-1, #BC.6-1). The application part is the new #BC.8-5-2-1 |
| #BC.5-1-0: C₁ = L³ was presented as VAR's printed value | It now says that VAR takes C₁ absolute (p.305 l.44), that we take C₁ = L³, its value for the base at p.280 l.20 (#T4.6), and that ε₁^G is §G's threshold at this C₁ |
| #BC.5-1-3-4-1: RG I p.253 l.14–16 describes the mean M, not the averages | It now says that the averages are built from RG I's mean M, an analytic function on G^c-sets of small diameter, and are defined at U_L(V) by #BC.5-1-3-4-1-1–-1-2 |
| Forward references to #BC.8-4-1 for 𝔤^c-valuedness | The lemma (*) is now #BC.5-1-1-1. #BC.5-1-3-1-2, -1-3, -4-1, -4-1-2, #BC.8-4-1 and #BC.8-5-1-1 cite it, or cite the Baker–Campbell–Hausdorff series. #BC.8-4-1 was rewritten on (*) |
| #BC.8-4: the case x ∈ Λ^X_0 was missing | "If x ∈ Λ^X_0, x is a point of 𝐁^X and w(x) = 1 (#BC.5)" |
| #BC.5-1-3-1: the CMP98 axial-gauge sentence and its "loop … bounds" clause were unclear | It now states CMP98's axial gauge from y (p.024 l.22–29, p.024 l.52–p.025 l.7) and the bound of A_{b′} by 2α₀ times the lattice distance from b′₋ to y on a coordinate box, which his telescoping proof gives. It was split at the new #BC.5-1-3-1-0 |

## Definedness sweep of BC (#BC.1–#BC.8), 8 Nov 2026
The user asked whether every object is defined. Each symbol of BC now has one of three sources: a definition in BC, a table row, or a pinned source line. Each pin was read in the corrected transcription.
- **New in #BC.1.**
  - #BC.1-0 gives the group: G ⊂ U(N) a Lie subgroup with 𝔤 Hermitian and G = e^{i𝔤} (CMP98 p.020 l.17, l.25–30), compact (#T12.27-1), and 𝔤^c (#T12.27-1-2-0). It also gives the operator norm (#T11.35), R(g)Y := gYg^{−1} (REG p.076 l.40; CMP98 (56)) and the gauge action (CMP98 p.027 l.2).
  - #BC.1-1-1 gives n-bonds and n-plaquettes (RG I p.251 l.27–28), p_{μν}(x) and its base point (REG p.076 l.41–42), U(∂p) (RG I p.252 l.8–12), and B(y) and 𝐆(y, x) (RG I (0.3)).
  - Δ_n(y) shows the scale (RG I p.251 l.23–24).
  - #BC.1-3 points to #BC.2-1 and #BC.2-1-3 for divisions and M.
- **Part a.**
  - #BC.4-3-1 had a real flaw: "above 2η" did not put the plaquette corners in X. It now uses the end-point in Ω^X_1, at distance above 3dLη from X^c, with corners within ℓ¹-distance 3η.
  - #BC.4-4-1's raw TeX W̄ = \overline{Ū^{j−1}} is now in words.
  - A^η is defined at #BC.1-4-2.
  - #BC.4-5-3-2-1 holds R(U₀), D^{η*}_{U₀}, HB, D(A′) and the fixed point of (61), pinned to REG p.080 and VAR p.285–p.287.
- **Part b.**
  - #BC.5-1 defines the norm of B and G^c, and #BC.6 cites #BC.1-0 for R. #BC.5-3-1 cites #BC.1-0 for the gauge action.
  - #BC.6-1 defines CRE's pair (𝐔, 𝐉) (#T11.10), ξ (p.260 l.20; η at the use, TL #52), M^·(𝐔) (#T11.7-0-2) with U_{p,X}(M^·(𝐔)) at 𝐔's data on 𝐁^X (#BC.1-5, #BC.3-1), and 𝐉_{p,X} (#T6.11-1). CRE prints no formula for 𝐉_{p,X}; #T6.11-1 records RG I's J_n of (1.15) (p.262 l.49–50), the construction CRE refers to at p.261 l.2.
  - #BC.8-2-1 defines x_l: x_n := y, x ∈ B^l(x_l), x_l ∈ B(x_{l+1}), and x₀ = x, matching CMP98 p.033 l.10 and (85).
  - #BC.8-2 and #BC.8-2-1-1 rename U₁ to U₁^X, which clashed with #BC.5-1-3-1-3's U₁. #BC.8-2-2's raw TeX \bar F₀^l is now "F̄₀^l, F₀'s average at the level l".
- **Lines.** #BC.5-1-1, #BC.5-1-3-1, #BC.5-1-3-3 and #BC.8-2-2 were split at sentence boundaries. Every line is now at most 600 characters, measured with Python. All BC tags cited in BC, the table, the TL, the LF and balaban_proofs/ resolve; only an archived triage file names deleted tags.
- **Messages.** The fork was told about #BC.1-0, #BC.1-1-1, #BC.5-1-1-1 and M^·. It added #T11.7-0, #T11.7-0-1 and #T11.7-0-2, and pointed #T12.27-1 to #BC.1-0 (table ff4f02f4ff76). The LF session (handover (4)) was told about D2.7 15.6(d).

## Pre-check of bp-crit-bc38a-20261108-r14 (full round of part a, effort high)
- **Lines re-read.** Every part a line was re-read with its definitions (sweep above). Two pins were read again: CMP98 p.033 l.10 and (85), and RG I p.262 l.2–50.
- **Changes to part a since the r13 repairs.** These are #BC.4-3-1 (the corner distance) and #BC.4-4-1 (W̄ in words); both were re-derived. The context lines #BC.1-0, #BC.1-1, #BC.1-1-1 and #BC.1-3 were checked against CMP98 p.020 l.15–31, p.027 l.1–12, REG p.076 l.38–42, and RG I p.251 l.14–28, p.252 l.6–32.
- **Second pass.** The r13 repair lines (#BC.4-3–#BC.4-3-2, #BC.4-5-2-1, #BC.4-5-3–#BC.4-6) had their second pass at 12:12 (above). #BC.4-3-1's new corner argument had its second pass now: an end-point in Ω^X_1 is at distance above 3dLη ≥ 3η from X^c, and the corners of p_ν and p′_ν are within ℓ¹-distance 3η of it.
- **Spec.** spec_bc38a_r14.json adds #BC.4-5-3-2-1 to the step list. Its SHAs are set at build.

## Recheck of the bc38b r13 repairs and pre-check of bp-crit-bc38b-20261108-r14 (full round of part b, effort high)
- **Pass 1.** Every line of #BC.5–#BC.8-5-2-1 was re-read after the repairs and the definedness sweep, and each bound was recomputed:
  - \|e^{iB} − 1\| < C₁ε₁ on r_B;
  - the axial-gauge box, with \|b′₋ − b₋\|α₀ ≤ ½(d + 2)L²B₃ε₁ ≤ ½ and \|A₀\| < (d + 2)L²B₃ε₁L^{2(j−n)}(L^jη)^{−1};
  - the rooms of (2.34)–(2.37) and their unit conversions;
  - f_n ≤ f_{m,n} for m ≤ k (TL #6.16.4-2);
  - Θ's exponent: each of w(x) and w(x)^{−1} has two v^X factors of norm at most e^{6d√Nt^X} and two path factors of total norm at most e^{d(t^X + t(B))/2}, so Θ ≤ e^{d(t(B) + (24√N + 1)t^X)};
  - (*) at #BC.8-5-1-1, in the variable ε^{dev} − ε^{dev}_0 on a ball about 0.
  - Pins read: CMP98 p.024 l.20–56 and p.025 l.1–8 (|A_b| < 2|b₋ − y|α₀ on Δ(p′); BC's box version is derived from his telescoping and is stated as such), CMP98 p.030 l.40–p.031 l.12 and p.033 l.36–50, RG I p.252 l.6–32, p.261 l.30–49 and p.262 l.1–63, and CRE p.260 l.20–50 and p.261 l.1–50.
  - No defect was found.
- **Pass 2.** The changed claims and their uses were re-derived, and this found two unclear sentences, repaired in place:
  - #BC.5-1-3-3 now names the j-bonds with both end-points in B^{j+1}(x), so S_b ⊂ B^{j+1}(x). That block is within ℓ∞-distance (1 + ½)L^nη of z, so #BC.5-1-3-1–-1-3 apply and give \|𝔮_j(b)\| ≤ 𝔞_j. These are (105)'s bonds, along 𝐆 contours inside Δ(x_{j+1}).
  - #BC.8-5-2 now names F(V) as the axial-gauge minimal configuration of 𝐁^X continued about W₀. This is Bałaban's construction of U_n(V) in the axial gauges for G^c-valued data (RG I p.262 l.42–43), which is CRE's U_{p,X} at the caller.
  - Both repairs were rechecked once more after the edit, as were the uses of BC tags: TL #6.16.3-2 and #6.16.4-2, and rows #T12.27–#T12.27-6-0. The fork updated #T12.27-5 and #T12.27-6 for #BC.8-2-1-1 and U₁^X (table 9ac099322946).
- **D2.7.** The LF session applied 15.6(d) ("within 2r^{ext}_k of a real datum at every datum of 𝐁_k on the support", D2.7 5dedf785fb28) and sent its own re-derivation, which matches #167-3.
- **Sizes.** Part a is 16.0k characters and part b 21.2k. Part b grew by the definitions of CRE's objects, the points x_l and the lemma (*); no line restates a row. Every line is at most 600 characters.
- **Specs.**
  - spec_bc38b_r14.json is new. It has the r13 review as its prior, a step list of all 53 part b tags, a question on each r13 finding, the caller's "at every datum of 𝐁_k", and rows #T11.7-0–#T11.7-0-2 and #T12.27-1–-1-2-1 as background. Its --check gave 0 conflicts with 33 allowed; U₁^X and BC's local x_n are allowed, the latter against #T4.49's x_n.
  - spec_bc2_r4.json has BC f1450fa57a1e, and its --check gave 0 conflicts with 7 allowed.
  - The LF SHA of both is reset at build.

## BP_LFR2_REPLACEMENT.md: citation check ahead of its first round (during bc38a r14)
- **Pins read against the corrected transcriptions, all correct:**
  - LFR II p.356 l.35–38, p.365 l.1–40, p.370 l.1–41;
  - LFR I p.195 l.3–9 and p.197 l.22–42;
  - CMP98 p.019 l.10–15 and p.026 l.44–53;
  - VAR p.278 l.1–10, l.44–48, p.279 l.8–16, p.301 l.42–46, and the tags (174), (175) at p.305 and (190) at p.308;
  - REG p.078 l.10–34 and p.089 l.15–37;
  - CRE p.255 l.14–18, p.256 l.58–62, p.264 l.50–53, p.269 l.6–13.
- **One definition added.** #160.2-2 used U_k^0 undefined. It now reads "U_k^0, (1.50)'s configuration at B = 0 (LFR II p.370 l.14)".
- **Setting lines added.** The new #160.0–#160.0-1 give each object a source:
  - Λ and U_{k,Z}, 𝔹_k(Z): LFR I (1.73)–(1.74), #T11.29;
  - Q_k^{s*}: #T11.28;
  - h = k − N: LFR I p.178 l.9;
  - Ω″_j and 𝐁″_k: LFR I (1.11)–(1.13), p.179 l.25–47;
  - Λ^{old}: #T12.2;
  - Y₁ and 𝐁_k″(Y₁): LFR II p.373 l.14–17;
  - V_h of 𝐓′_k(X): LFR II p.378 l.30–31;
  - U_0^{(AL)}: LFR I (1.86)–(1.87);
  - 𝓜: #124;
  - ε_k, K, M₀: #T3.27, #T4.48, #T4.30.
  All pins were read.
- **Later checks (12:45).**
  - CRE (1.3) (p.246 l.38–45) and (3.6) (p.266 l.2–9) were read, and each matches its use in #160.5–#160.5-1.
  - The cited LF tags exist and say what is cited: #3.84-1.1, #3.85.1, #3.85-1, #3.86, #3.86-1, #3.96-1-1, #4.44-0, #4.48-3.0.1 and #4.560.1. "BP #4.11" now names BP_LAYER_WIDTHS.md.
  - Several arithmetic steps were recomputed:
    - #160.7: 8MR_k − 2M₁ − 1 ≥ 7MR_k, and (190)'s e^{−δ₀d/8} split as e^{−δ₀d/16}·e^{−δ₀d/16};
    - #160.7-1: R_k ≥ (log g_k^{−2})²;
    - #160.8: 16dL^iη sup|ℋ^♭| ≤ 32dKM₀ε_k;
    - #160.8-2: the sum.
    Each holds.
- **Still to do before its round.** A full read of #160.3–#160.6 for unstated steps.
- **Found in that read (13:00).**
  - #160.4 asserts VAR (2) for U^♭ on Z from CRE (2.34) and (2.36), but does not give the step from (2.36)'s current J = D*η^{−2}π Im∂U to (2)'s D*∂U.
  - The structural repair needs (2)'s plaquette line only at the small ε₀^♭: CMP98 (54) uses (52) alone, and LF #3.86-1 uses Lemma 1's (1.7) alone. The Z-problem's space (6) needs both lines, but only at a fixed ε₀ ≤ a₀.
  - U^♭ is Theorem 1's minimal configuration at V^♭, so it lies in 𝔘_k(B₃a₁). The Z-problem's layers have larger rooms, since L^jη ≤ 1. The exception is the bonds whose REG (1.2) terms leave Z, which is BC #BC.4-3's partial-sum case.
  - #BC.4 itself does not apply: its 𝐁^X is a joined set with X ∈ 𝐃_m, X ⊂ Ω_{m+1}^c, and data at ε₁ ≤ ε₁^*. #160.4 therefore cites only the steps that carry over: data locality (#BC.3, generalised to 𝐁_k(X′) for X′ ⊂ Ω_k by #BC.3-6), the transforms (#BC.4-5-2-1) and criticality (#BC.4-5-3).

## Verdict: bp-crit-bc38a-20261108-r14

0 fatal, 1 serious, 4 minor. This was a full round of part a, #BC.3–#BC.4-6-1, built with LF 92b3e62044ba, table ff4f02f4ff76 and BC 680e9511032a. All four r13 findings are repaired, and #BC.3 is correct under BC's data convention of that time.

### Repairs (bc38a r14)

| Finding | Repair |
|---|---|
| #BC.4-5-3-4, serious. REG's two cases (p.081 l.33–34) omit the n-bonds from Λ^X_n into (Ω^X_{n+1})^{(n)}, which #BC.3-1 counted as data, so Y_s ∈ 𝔙(𝐁^X, W) was not shown. | The root cause was #BC.3-1's convention. Data at such bonds contradict REG's invariance of 𝔙 under (1.14) (p.078 l.13–17), since u at the inner end-point is free, and they contradict table row #T11.19, which records that the unit bonds from Λ₀ into a coarser layer are not data. #BC.3-1 now defines the data bonds as the n-bonds whose end-points have index n, or n and n − 1, or, at n = 0, lie outside Ω₀. These are REG's two cases inside Ω₀. The new lemma #BC.3-1-2 shows that an n-bond from a point of index n to a point outside Ω^X_{n+1} is a data bond, by VAR (1). #BC.3-3, #BC.3-3-1 and #BC.3-5 use it. #BC.4-5-1 now lets U_Y differ at every bond with an end-point in Ω^X_1, and its plaquettes stay in X. #BC.4-4 and #BC.4-4-0 name the data bonds. The chart argument #BC.4-5-3–#BC.4-5-3-5 is replaced by a criticality lemma, #BC.4-5-3. It uses the local minima of #BC.4-5–#BC.4-5-2-1 and VAR's notion of a critical point, a vanishing derivative in every tangent direction (p.278 l.32–33, p.290 l.39–47). #BC.4-6 applies Theorem 1's uniqueness of the critical orbit in (6) (p.279 l.8–15) at B₃ε₁^X ≤ ε₀^X ≤ a₀ (#BC.4-1-2). |
| #BC.4-4, minor. The reading of (7) at plaquettes with an uncovered bond was implicit, and W was not said to be G-valued. | #BC.4-4-0 takes (7) at such plaquettes as the bound on Ū^j(∂p′) that #BC.4-4-1–#BC.4-4-3 prove. #BC.4-4 states that W is G-valued, by RG I (0.9) (p.253 l.30). |
| #BC.4-5-3-5, minor. (41) and RD*A_s = 0 were not cited. | The line is deleted with the chart argument. |
| #BC.4-5-3-2, minor. The G-valuedness of Ū̄₁^j had no source. | The line is deleted with the chart argument. |
| #BC.4-5-3-3, minor. p.281 l.2–7 does not state the G-valuedness of e^{iηA_X}. | The line is deleted with the chart argument. |

- **Recheck, pass 1.** Every changed line was re-read: #BC.3-1, #BC.3-1-0, #BC.3-1-2, #BC.3-3, #BC.3-3-1, #BC.3-3-2, #BC.3-5, #BC.4-4, #BC.4-4-0, #BC.4-5-1, #BC.4-5-3, #BC.4-6 and part b's #BC.6-1.
  - #BC.3-1-2 at n ≥ 1: L^nη < R′M′L^{n−1}η, as R′M′ ≥ 3dL. T^{(n)} ⊂ T^{(n−1)} holds for L odd. A point of T^{(i)} in B^i(z) is z, by #BC.2-1-1.
  - At n = 0, (H) excludes the other end-point from Ω^X_1.
  - In #BC.3-5, the end-points of a data bond of 𝐁 lie outside Ω_{n+1} ⊃ Ω^X_{n+1}.
  - The m^X = 0 case and #BC.4-6-1 keep their data at the bonds leaving X.
- **Recheck, pass 2.**
  - Theorem 1's hypotheses for 𝐁^X follow from #BC.4-1-2.
  - U⌈X lies in (6) by #BC.4-3 and #BC.4-5.
  - #BC.4-4-1's (j−1)-bonds of the average lie in cubes inside Ω^X_{j−1}∖Ω^X_j, so both of their end-points have index j − 1.
  - No live file states the old convention.
  - Part a is 14.6k characters, and no line exceeds 600.
- **Bookkeeping.** Table row #T12.27-1-2 records U₀^X with a citation of #BC.4-5-3, but U₀^X no longer occurs in BC. This was sent to the table's owner.
- **bc38b r14** was launched at 12:57, before this repair, with BC 4f057a738b26 (task bwx7wrjk2). Its snapshot still has the old #BC.3-1 in context.

## LFR2 #160.3-2–#160.4-3-3 repair (13:08–13:20)

- **#160.3-2.** REG (1.21) gives ∂(e^{iηℋ^♭}U)(p) = aU(∂p)b, with a, b unitary and ab = REG (1.22)'s ∂_U e^{iηℋ^♭}. VAR (25)'s ∂_0U_1((p)_z) is the cyclic product ba, so |ab − 1| = |ba − 1|, which is now stated. Then |aU(∂p)b − 1| ≤ |U(∂p) − 1| + |ab − 1|, since a(U(∂p) − 1)b + (ab − 1) and a, b are unitary. The quadratic and higher terms are O(η²|ℋ^♭|²) for η|ℋ^♭| ≤ 1.
- **#160.4, #160.4-0.** The line was 622 characters and is split. The layer is now Ω_k ⊃ Z, together with the points next to Z (#160.6-1), so the plaquettes leaving Z are covered. CRE (2.34) was checked at n = j = k: (1 − β·0)α_{0,k}ξ²(L^kξ)^{−2} = α_{0,k}η², times 3 (#157-2, #6.13). VAR (2) was checked at p.278 l.5.
- **#160.4-1.** The top-down sketch is replaced by BC #BC.3 with the new #BC.3-6, under which configurations equal off Z with equal 𝔹_k(Z) data have equal 𝐁_k data. It needs Z ⊂ Ω_k (#160.2), a union of M₁-cubes.
- **#160.4-2.** This now uses the #BC.3-1 index-0 data convention. The varied bonds have an end-point in Ω_1(Z), and dist(Ω_1(Z), Z^c) ≥ M₁Lη > 2η (#BC.2-2, #T2.15, where M₁ ≥ 12d + 1), in every metric of #BC.1-2, each at most ℓ¹. The claim "supported in Ω_1(Z)" was wrong for bonds from Z∖Ω_1(Z) into Ω_1(Z) and is replaced.
- **#160.4-3, #160.4-3-1.** The boundary bonds are rederived: both of their end-points lie within ℓ¹-distance 2η of Z^c. The partial sum satisfies 2(d − 1)B₃a₁η < B₃a₁η^{−1}, since 2(d − 1)L^{−2} < 1 (#T1.3). "ε₀ := B₃a₁" is now "ε₀ = B₃a₁".
- **#160.4-3-2, #160.4-3-3.**
  - The local-minimum argument is now explicit, as in BC #BC.4-5-2: (8) is given by finitely many strict inequalities, the data are kept (#160.4-1), and the actions are equal (#160.4-2).
  - Theorem 1 is applied at ε₁^♭ ≤ a₁ itself, with B₃ε₁^♭ ≤ B₃a₁ = ε₀ ≤ a₀; #160.3's ε₁ and #T3.20 are no longer needed.
  - VAR's standing conditions for 𝔹_k(Z) are #BC.3-6-1.
- **#160.6-2.** "REG's α₀ := ε₀^♭" now reads "ε₀^♭ … as REG's α₀" (no ":=" for REG symbols).
- **Recheck 1 (each touched symbol).**
  - ε₀^♭ is used at #160.4-0 and #160.6-2 only, as a plaquette bound.
  - ε₁^♭ is used at #160.4-3-3 only.
  - A^Z is new, with no clash in the note, TL or table.
  - "Z-problem's space" means (6) at ε₀ = B₃a₁ (#160.4-3-1) throughout #160.4-3-2–#160.4-3-3.
  - #160.5 uses U^♭⌈_Z = U(𝔹_k(Z), ·) up to VAR (4)'s group, matching #160.4-3-3.
- **Recheck 2 (pins).** Each pin was re-read against the claim: REG p.079 l.17–28; VAR p.282 l.4–19, p.278 l.1–48, p.279 l.8–15, p.305 l.31–36, p.309 l.8–14; CRE p.261 l.13–19 ((2.34)) and p.256 l.43–63. Prop 9 calls U_k(V′V₀) "the minimal configuration", so V^♭ satisfies (7) at some ε₁′ ≤ a₁; this is accepted in VAR's own setting (#167-4).
- Lines ≤ 600. LFR2 88dea0f09a94, BC (with #BC.3-6) see below.
- **Found in the full read of #160.5–#160.8 (13:25).**
  - #160.5: Proposition 9's ball (172) must be at a fixed ε₁. After #160.4-3-3 dropped #160.3's ε₁, the text named none. It now says #160.3's fixed ε₁, at which U^♭'s data satisfy (7), as ε₁^♭ ≤ ε₁ for g small. Then |B^♭| = O(d²)ε₀^♭ → 0 lies inside.
  - #160.6 (wrong as stated): |B^♭| was claimed invariant under REG's (1.14) applied to U^♭. But (1.14) for 𝐁_k fixes only the points of 𝐁_k, the k-centres on Z, and so changes U^♭'s j-averages (j < k) in the strip, which are data of 𝔹_k(Z). In LF #3.86 the step is valid only because □^{∼4} lies in 𝔹_k(Z)'s deepest domain.
  - Structural repair: #160.3-1 now takes U^♭, once and globally, as the element of the minimal orbit in REG's axial gauge (1.15) for 𝐁_k. The (1.14)-transformation from VAR's axial representative is 1 at the block points, so G^♭'s bound at those points stands, and #160.4 holds for every configuration of the minimal orbit. #160.6 then uses only w, constant on k-blocks and applied to both data. w conjugates both data at c by w(c₋), w(c₊) (CRE (1.3), RG I (0.6)), so B^♭(c) ↦ R(w(c₋))B^♭(c). w keeps (1.15), whose conditions are Ū^{j−1}(Γ) = 1 inside blocks. #160.6-2 applies LF #3.86-1 to (U^♭)^w.
  - Recheck: #160.8 uses G^♭ only at the k-centres (unchanged), and G = G^♭u^♭u_0 stays G-valued. #160.6-2's α₀ is LF #3.84-1.2's normalisation (|∂U − 1| < α₀η²), met by ε₀^♭ on Ω_k ⊃ □. Its α₁ is LF #3.86-1's start |V^w − 1|, at most 3(d − 1) plaquettes times O(1)ε₀^♭. The TL cites only #160.1, which is unchanged. LFR2 is 092dee38fa6c, lines ≤ 600.
- **Bookkeeping (13:35).**
  - #160.0's "Λ^{old} := … (#T12.2)" restated a table row, and "𝐁_k″(Y₁) := …" set a symbol of LFR II with ":=". Both are now plain identifications: "is", and "is LFR II's".
  - LFR2 is b3fba0de27d6.
  - The TL and LF tags that LFR2 cites all exist; the semantic check of #105–#106, #41.1, #43, #124, #134, #159, #161, #5.3 and #5.6 is done.
  - spec_lfr2_r1.json (first full round) passes --check with 0 conflicts (6 same-file allows). It launches after the BC rounds.

## Verdict: bp-crit-bc38b-20261108-r14

0 fatal, 0 serious, 7 minor. Snapshot BC 4f057a738b26, which predates the #BC.3-1 data-bond repair (part a). Not clean.

| Finding | Repair |
|---|---|
| 1 #BC.8-5-2: the base of the axial gauge is unfixed | #BC.5-1-4-1 now fixes F₀ in the minimal orbit at W₀ and defines F in Ax(𝐁^X, F₀); #BC.8-1 sets F₀ = F(V₀). The new #BC.8-5-2-0–#BC.8-5-2-0-2 take U^d in Ax(𝐁^X, F₀′) for any F₀′ = F₀^u of that orbit. By REG (1.19)–(1.20) and RG I (0.6), the condition is covariant: each product becomes R(u(x_{n+1})) of itself. So U^d = F^u with u G-valued and independent of V, and the bounds on ∂ and J are unchanged (#BC.6, #BC.7-1). |
| 2 #BC.5-1-3-4-1-2: BCH convergence is unchecked | Replaced by (*): ψ(ηA, −ηA₀) is analytic in B, and at 𝔤-valued B near 0 it is (1/i)log of an element of G near 1, hence 𝔤-valued. |
| 3 #BC.8-5: "on the support" | #167's "on the support" qualifies the real datum V_k⁰, not the bonds. #BC.8-5 now says so, and the comparison is at every datum of 𝐁_k, as #167 states. |
| 4 #BC.5-1-1-1: the inner product and the source of 𝔤-valuedness | Names CMP98's tr X*Y (p.020 l.31–35), whose orthogonal projection is ℂ-linear. 𝓗 is 𝔤-valued at 𝔤-valued B near 0, by VAR p.281 l.1–10 and p.307 l.2–5. |
| 5 #BC.5: forward use of 𝒱, U_L and F | The statement now describes V, U_L and F in words, with a pointer to where each is fixed. The forward reference to #BC.8-4-1 is dropped. |
| 6 #BC.6-1: the ξ citation | ξ is cited to p.260 l.18–20, and L^{−m} to p.256 l.57–58 and #T11.27-1. The sentence is split. |
| 7 #BC.5-1-3-1-0: a strict inequality | Now ≤. The strict bound on A₀ is kept through #BC.5-1-3-1: the points of S_b lie at ℓ¹-distance below (1 + d/2)L^jη, since L is odd. |
| Q8 #BC.5-1-3-1-2, #BC.8-4-1 | #BC.5-1-3-1-2 is split into one fact per sentence (and -2-1). In #BC.8-4-1, "up to the factor i" becomes "(1/i)log h_l and (1/i)log κ". |

- **Recheck 1.**
  - F₀ is first used at #BC.5-1-4-1, where it is defined. #BC.8-1 no longer defines it.
  - The only definition of U_{p,X}(W₀) or F₀ is the one in #BC.5-1-4-1.
  - #BC.8-4-1's reference to #BC.5-1-3-4-1-2 holds the ψ claim again.
  - |A|₂ ≤ √NLt(B)(L^jη)^{−1} ≤ ½ρ₀(L^jη)^{−1} follows from 2√NLt(B) ≤ ρ₀ (#BC.5-1-3), and |A₀|₂ ≤ ρ₀(L^jη)^{−1} from c^X ≤ ρ₀/((d + 2)√N) (#BC.4-1-1).
  - The relative average transforms by R(u(c₋)), and the path product by u(x)·u(b₋)^{−1}.
- **Recheck 2.**
  - #BC.3-6 was checked against each use of 𝐁^X in #BC.3-1-2–#BC.3-5. These use (H) and the partition (#BC.3-3), #BC.2 (#BC.3-4, #BC.3-5: Ω_{n+1}(X′) ⊂ Ω_{n+1}, since B^i(y) ⊂ Ω_k ⊂ Ω_i), and VAR (1) (#BC.3-1-2, #BC.3-4-1). (L^{n−1}η)^{−1}dist ≥ LM₁ > R′M′ > L.
  - The partition follows by (C), from both directions.
  - The pins were re-read: VAR p.281 l.1–10, p.307 l.1–6, p.280 l.40–47; REG p.079 l.1–16; CRE p.256 l.43–63, p.260 l.10–24.
- BC 6d00f1a4a44e, lines ≤ 600. Both parts are at clean count 0. bc38a r15 comes next, then bc38b r15 (full).

## Pre-check: bp-crit-bc38a-20261108-r15 (full round of part a, effort high)

- I read the whole of part a (#BC.3–#BC.4-6-1) myself. Every line was re-read, including the new #BC.3-6–#BC.3-6-1, and no unstated step was found.
- Part a is 15,404 characters, up from 14.6k by #BC.3-6 (new content for LFR2). Part b is 23,115 characters, under 25k.
- Touched symbols:
  - X′ occurs only in #BC.3-6–#BC.3-6-1.
  - 𝐁_k(X′) is #BC.2-2's 𝐁_q(X) at q = k.
  - R′, M′, M₁ and K are as in #T2.5, #T2.7 and #T2.15.
  - The definition check reports 0 conflicts (11 allowed).
- Cited displays: CRE p.256 l.43–63 and p.257 l.1–5, quoted above; VAR (1) via #BC.3-1-1. The inequality directions were checked: dist ≥ LM₁·L^nη > R′M′·L^nη, as LKM′ > (LK − 1)M′.
- Spec: LF 16a7cb388027, BC 6d00f1a4a44e. The claim, the caller (LFR2 #160.4-1, #160.4-3-2–#160.4-3-3), the step list and Q3 now include #BC.3-6. No known weak point remains.

## Handover

- 2026-11-07 02:57: r29's pre-read is done apart from the LF lines; two pair repairs (e83d6e64f297); links-a's extracts are extended.
- 2026-11-08 00:33: all of bc38 r6's eight minor findings are repaired (BC 2c6ce50f8386), and TL #169's c_π is fixed (4dcc8ac2b48e). r7 was launched at 00:32 as task b2gd0zeua (one package, effort high). After it: two consecutive clean rounds, then BC.2 r4 and BP_LFR2_REPLACEMENT.md's first rounds. TL #169 goes to TL's next content round.
- 2026-11-08 01:05: bc38 r7 had 5 minor findings, all repaired, and the pre-check repaired #BC.5-1-0 (BC d7cb3e924234; TL #94 6c97421f37d0). BR fecfa5745a94 was re-derived against BC, and only #BC.3-1-1-2's citation changed. r8 was launched at 01:05 as task br9h8kvy9 (one package, effort high). The clean count is at zero.
- 2026-11-08 01:23: bc38 r8 had 2 minor findings, both repaired (C₁ = L³ and B₃ ≥ 1, #BC.5-1-0-1; M2's derivation), BC 034a8d0c7b55, table 565d0ca22a72. BC.2's Ω_p description is settled (#BC.2-3-1, #BC.2-3-1-1), and spec_bc2_r4.json is written. r9 was launched at 01:23 as task bkbhe2shc. The clean count is at zero.
- 2026-11-08 01:57: r9 was stopped by the user, and r10 ran after a full recheck. It had 4 minor findings and an observation (REG (1.33)'s α₀ at the base U₀^X), all repaired. Three recheck passes were made, the third with no defect. BC is a721e71ba8f9 and the table 5ffb7cad1762 (the fork's rows #T12.27-1, #T12.27-1-1 and #T12.27-1-3). r11 was launched at 01:56 as task badtj1r3c, effort high. The clean count is at zero.
- 2026-11-08 02:35: the user stopped r11 at 01:59, and the full hypothesis recheck of #BC.3–#BC.8-5-2 is done. It found five defects (ε̄₃ without p.293 l.46–48, c_γ ≥ 1, the p.309 pins, #BC.8-4-1's "there", and B's 𝔤^c-valuedness at the extension points), all repaired in place, with two recheck passes and no further defect. BC is bd791c479a27 and the table 7e04c266ddd5 (the fork's #T12.27-1-1, #T12.27-1-1-1, #T12.27-1-2, #T12.27-6 and #T12.27-6-1). r12 was launched at 02:35 as task bi2obaspk, effort high. The clean count is at zero.
- 2026-11-08 02:58: the user stopped r12 and had the package condensed (see "Rework of #BC.3–#BC.8 after r12 was stopped"). BC is 12fcb3b7f8ba, 33.9k characters, down from 40.3k, and TL is 14bce2a70216 (#94). The package is split into bc38a (#BC.3–#BC.4, 14.6k) and bc38b (#BC.5–#BC.8, 19.2k). spec_bc38a_r13.json and spec_bc38b_r13.json pass --check with 0 conflicts. Each part is waiting for the fork's table rows; then a is launched, and b after it. The clean count is at zero for both parts.
- 2026-11-08 11:42: bc38a r13 was launched without waiting any longer for the table. The spec tells the referee not to use rows #T12.27-1–#T12.27-1-3 and that the file's definitions govern; spec b says the same. The packet was built with LF 2fb3f5358bf1, table 6d09b1b5054d and BC 12fcb3b7f8ba. Its argument is 26901 characters, of which the reviewed blocks are 14.6k and the rest is #BC.1–#BC.2 context. r12's argument was 52544. The task is b1rwqcjds, effort high. bc38b r13 goes next, after a's report.
- 2026-11-08 11:50: during bc38a r13, #BC.1–#BC.2 had their full pre-check for BC.2 r4. Every line was re-read, and (C), (G), (S) and #BC.2-3–#BC.2-6-1 were re-derived. CRE p.257 l.1–26 and RG I p.251 l.12–16 were read: L is odd and > 11, so 2d < 13 ≤ L. The check found one unpinned claim: #BC.2-3-1-1's distance at Ω_p is (2.14)'s hypothesis at j = p, and the pin CRE p.257 l.7–11 is now added. spec_bc2_r4.json gets its SHAs at build time.
- 2026-11-08 12:04: bc38a r13 returned 0 fatal, 0 serious and 4 minor findings, all repaired in place and rechecked twice (see "Verdict: bp-crit-bc38a-20261108-r13"). BC is c1e9157106d9. The fork re-pointed #T12.27-5. bc38b r13, a full round of part b, was launched at effort high (task bfqsbhsm2), built with LF a51211571c45, table 0d3d5af5c96b and BC c1e9157106d9; its argument is 29076 characters. Next come bc38a r14 (a full round of part a) and BC.2 r4.
- 2026-11-08 12:34: bc38b r13 returned 0 fatal, 0 serious and 8 minor findings, all repaired in place (see "Repairs (bc38b r13)"), and BC had its definedness sweep. TL #167 and #167-3 now read "at every datum of 𝐁_k" (TL d4f21a03f974). The LF session was sent D2.7 15.6(d)'s wording. bc38a r14, a full round of part a, was launched at effort high (task br5q9b4za), built with LF 92b3e62044ba, table ff4f02f4ff76 and BC 680e9511032a; its argument is 29401 characters. While it runs, part b gets its two recheck passes for bc38b r14, then BC.2 r4 waits its turn.
- 2026-11-08 12:42: part b's two recheck passes are done (see "Recheck of the bc38b r13 repairs…"), and spec_bc38b_r14.json is ready. The LF session pointed out that "datum" was used both for the whole real configuration and for one bond's value. TL #167 and #167-3 now read "at each bond of 𝐁_k" (TL 4516a8f617ad), as D2.7 does (4a09176784cc). BC #BC.8-5 reads "at each bond of 𝐁_k that carries a datum", which is BC's per-bond use of "datum" (#BC.3-1), and #BC.1-4-2 says "about real regular data" (BC e800a995c236). BP_LFR2_REPLACEMENT.md has its pins checked and the new setting lines #160.0–#160.0-1 (f932fb486ed0).
- 2026-11-08 13:05: bc38a r14 returned 0 fatal, 1 serious and 4 minor findings. All are repaired, and the repairs were rechecked twice (see "Verdict: bp-crit-bc38a-20261108-r14"). BC is bcca1b1cd7f1: its data-bond convention is now REG's and #T11.19's, and the chart argument is replaced by Theorem 1's uniqueness of the critical orbit. The table is 6016c4168077 (the fork's #T12.27-1-2). bc38b r14 was launched at 12:57 (task bwx7wrjk2). spec_bc38a_r15.json passes --check and goes next. Then come BC.2 r4 and the LFR2 #160.4 repair, with #BC.4 cited.
- 2026-11-08 13:23: the LFR2 #160.3-2–#160.4-3-3 repair is done and rechecked twice. #BC.4 is not cited; the cited steps are #BC.3, #BC.3-6, #BC.4-5-2-1 and #BC.4-5-3. LFR2 is 88dea0f09a94. bc38b r14 returned 0 fatal, 0 serious and 7 minor findings, all repaired and rechecked twice. BC is 6d00f1a4a44e. bc38a r15 (full) was launched at 13:22 (task b2gjte2pu) on LF 16a7cb388027 and table 47f87bcff833, and the SHAs and new tags were sent to the fork. Next: bc38b r15 (full), BC.2 r4, then the LFR2 first round. The full read of #160.5–#160.6 is under way.
- 2026-11-08 13:36: bc38a r15 (full) returned 0 fatal, 0 serious and 4 minor findings, so part a's clean count stays 0. The findings are not yet repaired:
  - #BC.3-1: the n = 0 "outside Ω₀" data clause needs a source (VAR p.277 l.17 with LFR I p.190 l.14–15) and a sentence restricting the acting group to u = 1 on X̂∖X (as #BC.4-6-1 shows); the citation p.081 l.33–34 should be l.33–35.
  - #BC.4-4-0: state that VAR's printed (7) defines nothing at an uncovered p′, so the bound on Ū^j there is extra information; name "first kind" and "second kind" as #BC.4-4's data bonds of index j and its bonds with both end-points in Λ^X_{j−1}.
  - #BC.4-5-3: cite p.278 l.32–33 and Theorem 1 for criticality on (6), and p.290 l.6–8 for VAR's passage to 𝔉, in place of p.290 l.39–47.
  - #BC.4-6: add the line that #BC.4-3's space is an open subset of VAR's space (6) under every reading of (2), so local criticality carries over and Theorem 1's uniqueness applies.
  Next: repair these four in place, recheck twice, then rebuild and launch bc38a r16 (full), then bc38b r15, BC.2 r4 and LFR2 r1.
- 2026-11-08 13:38: the fork moved the table to 087d1a0f1f7d and LABELS to b23a187cc92a (BETA's §10 rows; #T10.29's F(x_0) is now f_K, and #T10.35's K_R is now K_V). The table hash was checked. TL's K_R (#14, #166) is #T2.24's λ_R = K_RLM + 1, not §10's, and BC, LFR2 and the pair note cite no §10 row, so nothing in my files changes. No spec pins the table SHA.

## Verdict: bp-crit-bc38a-20261108-r15

0 fatal, 0 serious, 4 minor (full round of #BC.3–#BC.4-6-1 on BC 6d00f1a4a44e). Not clean; part a's count stays 0.

Repairs (BC ef2364040962):

- #BC.3-1 (n = 0 clause for bonds leaving Ω₀): the source and the group are now the lemma #BC.3-1-3. Such a bond has its inner end-point in Λ₀ (VAR (1)). It is a data bond by VAR (3) at j = 0, since Λ₀ stands for the bonds with an end-point in it (p.277 l.17). If Y and Y^u both lie in 𝔙, then Y(a, b) = Y(a, b)u(b)^{−1} (#T10.23), so u(b) = 1. The orbits in (6) are those of the subgroup that is 1 at the outer end-points too. #BC.3-1 points to #BC.3-1-3, and #BC.4-6-1 now cites it in place of its own argument. The citation is now p.081 l.33–35 (checked: REG file l.36 is printed l.35, the second case).
- #BC.4-4-0: VAR defines no (∂W)(p′) at a p′ with an uncovered bond (p.278 l.39–44), so (7) is no condition on W there, and the bound there is on U. "First kind" now reads "the data bonds of index j". In #BC.4-4-1, "second kind" now reads "a bond of ∂p′ with both end-points in Λ^X_{j−1}".
- #BC.4-5-3: VAR's notion is now cited as printed. The derivative vanishes on the tangent space (p.290 l.39–47, for 𝔉), and Proposition 2 reduces the critical orbits in (6) to 𝔉 (p.278 l.32–33, p.290 l.6–8). The tangent vectors in the space are the velocities of curves. The proof's second half is now #BC.4-5-3-1 (line length).
- #BC.4-6: #BC.4-3's clause now ends "an open condition implying any bound (2) on one such sum". #BC.4-6 quotes Theorem 1 with (2) at the layer-0 bonds taken as any one such bound. #BC.4-6-0 shows that 𝔘 ∩ 𝔙 is an open subset of (6) containing the orbit (#BC.4-5-2-1). The orbit is critical there, hence in (6).
- Consumers: #BC.5-3-1 now cites #BC.4-6-1 for w = 1 at X̂∖X. LFR2 #160.4-3-1–#160.4-3-3 carry the same two points for 𝔹_k(Z): the open subset (as in #BC.4-6–#BC.4-6-0), criticality via #BC.4-5-3–#BC.4-5-3-1, and the group 1 at the outer end-points (#BC.3-1-3). LFR2 is now c1d19be773aa.

Recheck 1: #BC.3–#BC.4-6-1 reread in full against VAR p.277 l.10–26, p.278 l.1–48, p.279 l.1–16 and p.290 l.1–47; all lines ≤ 600.

Recheck 2: every use of #BC.4-5-3, #BC.4-6, #BC.4-6-1, #BC.3-1-3, "first kind", "second kind" and X̂∖X was grepped in BC, LFR2, the table and TL. The two re-pointings above were made. Table #T12.27-1-2 still cites p.081 l.33–34; this was sent to the fork.

## Pre-check: bp-crit-bc38a-20261108-r16

- Every changed line was reread (#BC.3-1, #BC.3-1-3, #BC.4-3, #BC.4-4-0, #BC.4-4-1, #BC.4-5-3, #BC.4-5-3-1, #BC.4-6, #BC.4-6-0, #BC.4-6-1). The cited displays were quoted: VAR (1), (3), (4), (6), p.277 l.17, Theorem 1 p.279 l.8–15, and p.290 l.6–8 and l.39–47.
- No new constant or symbol was introduced. The definition check reports 0 conflicts (11 allowed).
- Part a was 15,404 characters and is now 16,479, under 25k. The growth is the new lemma #BC.3-1-3 and the open-subset step, which is new mathematics, minus #BC.4-6-1's old argument.
- No known weak point remains. Launching the full round r16.

## Repairs made while bc38a r16 runs (13:50)

- #BC.8-5-2-0-1 and #BC.8-5-2-0-2 are part b and not under review in r16. They said u keeps the data "as u = 1 at the points of 𝐁^X", which missed the bonds leaving X. Now u is equal to 1 also at X̂∖X, and Y^u has Y's data because u = 1 at both end-points of every data bond (#BC.3-1-3). BC is now c25482227c42.
- In LFR2, my full read of #160.0–#160.8-2 for its first round found one imprecise step. #160.4-3 said U^♭ lies in (8) "for a value ε₁′ ≤ a₁ at which V^♭ satisfies (7)", with no source. Now it lies in 𝔘_k({Ω_j}, B₃(1 + 4C₁)ε₁), as (173) is p.281 l.19's ε₂ with ε₀ = B₃(1 + 4C₁)ε₁ for U_k(V′V_0). #160.3 fixes ε₁ small enough for §G (p.305 l.36), with (1 + 4C₁)ε₁ ≤ a₁, and names C₁ as VAR's absolute constant (l.44). C₁ in the table (#T3.24, #T3.26) is the same constant. The rest of LFR2 re-derives correctly. That covers the composite G of #160.8, the factor at the outer k-centre in #160.8-1, and the sum of phases in #160.8-2. LFR2 is now ac279d225142.
- The specs spec_bc38b_r15, spec_bc2_r4 and spec_lfr2_r1 now carry BC c25482227c42 and LFR2 ac279d225142. bc38b's context extract now ends at #BC.3-1-3, and LFR2's permitted background and claim name #BC.3-1-3, #BC.4-5-3-1 and #BC.4-6-0. All three --check runs give 0 conflicts.
- The fork fixed #T12.27-1-2 (p.081 l.33–35, with a pointer to #BC.3-1-3). The table is now 2b7997cee899 and LABELS bf60cc5e0458.
- Before BC.2 r4's full round I read all of #BC.1–#BC.2-6-1 and re-derived (C), (G), (S), #BC.2-3-3, #BC.2-4 and #BC.2-5 under each boundary convention. Two repairs:
  - #BC.2-4-2 hard-coded d = 4 ("2d < 13 ≤ L"). It now reads "2d < L (#T1.3), so within distance below M₁L^{q+1}η".
  - #BC.2-3-3's second alternative fails for ∂X = ∅ (X = T_η). It now assumes ∂X non-empty. In case (c) of #BC.2-3-2, ∂X is non-empty because (S) gives a point of T_η∖X near y ∈ X. #BC.2-6-1 now cites #BC.2-3-2 for q ≤ m.
  BC is now 3fa7d11fafd7, and spec_bc2_r4 and spec_bc38b_r15 carry it.
- I read all of part b (#BC.5–#BC.8-5-2-1) before its full round. That covers #BC.5-2-2's use of #BC.4 at any configuration of the minimal orbit, the use of #BC.3-1-3 in #BC.8-5-2-0-1 and #BC.8-5-2-0-2, #BC.8-2-1's v^X = 1 on Λ^X_0 (VAR p.281 l.2), and #BC.8-4's Θ = 1 at X̂∖X. No further gap found.
- LFR2 #160.3's C₁ now cites #T4.6, VAR's absolute C₁ of (14) and (172)–(173). The fork confirms the same C₁ as #T3.24 and #T3.26. LFR2 is now d16143b8f96e, and spec_lfr2_r1 carries it, with #T4.6 among the rows.
- 2026-11-08 13:55 (handover): bc38a r16 (full, effort high, task b3dmfzq98) is running on BC ef2364040962. The BC edits made since are outside its extracts. BC is 3fa7d11fafd7, LFR2 d16143b8f96e, the table 2b7997cee899 and LABELS bf60cc5e0458. Part a's clean count is 0, part b's 0, BC.2's 0 and LFR2's 0 (not yet reviewed). Next: triage r16, then bc38b r15 (full), BC.2 r4 (full) and LFR2 r1, one at a time.
- 2026-11-08 14:01: the fork reports table dddfdf3806d9, LABELS b223ce5e35c7 and LF d89bf93c0fa0; the only row change is #T12.7-18, which no file of mine cites. LF hash checked. Every LF tag cited by BC and LFR2 is still present: #3.84, #3.84-1.1, #3.85, #3.85.1, #3.85-1, #3.86, #3.86-1, #3.87, #3.96-1-1, #4.44-0, #4.48-3.0.1 and #4.560.1. spec_bc38b_r15, spec_bc2_r4 and spec_lfr2_r1 now pin lf_sha d89bf93c0fa0, and their --check runs give 0 conflicts.

## Verdict: bp-crit-bc38a-20261108-r16

r16 was the full round of #BC.3–#BC.4-6-1 on BC ef2364040962. It found 0 fatal, 0 serious and 3 minor problems, all wording or attribution; the mathematics is correct throughout. The round is not clean, so part a's count stays 0.

Repairs (BC feeaabbb7d6c):
- #BC.3-1-3: "they keep 𝔙" read as circular. The converse now has its own line, #BC.3-1-3-1: a (4)-transformation equal to 1 also at the outer end-points is 1 at both end-points of every data bond (#BC.3-1), so it keeps 𝔙 (#T10.23). VAR's invariance of 𝔙 (p.278 l.15–16) holds for this subgroup. The (4)-orbit of a configuration of (6), intersected with (6), is its orbit under the subgroup, and these are the orbits of which (6) is a union (p.278 l.32). The index-0 equation now cites #BC.1-0 instead of #T10.23.
- #BC.4-4-0: "VAR defines no (∂W)(p′)" rested on #BC.3-1, not on the print. It now says that the uncovered bond carries no datum (#BC.3-1), so the product of p.278 l.39–44 is not formed and (7) is no condition on W. At the other p′, the bound on U is what (7) asks where a bond from Λ^X_j into (Ω^X_{j+1})^{(j)} carries Ū^j as a datum, as p.277 l.17 would give. "W = Ū^j at the data bonds" moved to the head of #BC.4-4-1, and "wherever VAR defines it" there now reads "wherever it is formed".
- #BC.4-3: the convention now stands in its own sentences after the lemma statement, with the attachment of "defined on X̂" fixed. The plaquette proof is the new #BC.4-3-0.
- Consumers: #BC.4-6-1, #BC.8-5-2-0-2 and LFR2 #160.4-3-3 now cite #BC.3-1-3–#BC.3-1-3-1. LFR2 is 2c5cda85d782.

Recheck 1: the changed lines (#BC.3-1-3, #BC.3-1-3-1, #BC.4-3, #BC.4-3-0, #BC.4-4-0, #BC.4-4-1) were reread against VAR p.277 l.17, p.278 l.15–16, l.32 and l.39–44. Both directions of the orbit identity were re-derived. All lines are ≤ 600 characters.

Recheck 2: every use of #BC.3-1-3, "VAR defines", #BC.4-3 and #BC.4-4-0 was grepped in BC, LFR2 and the table. #BC.4-5, #BC.4-5-2-1 and #BC.4-6-0 cite #BC.4-3 as the lemma, which is unchanged. LFR2's "#BC.4-3–#BC.4-3-2" range now includes #BC.4-3-0.

## Pre-check: bp-crit-bc38a-20261108-r17

- spec_bc38a_r17 is at BC feeaabbb7d6c and LF d89bf93c0fa0. The step list adds #BC.3-1-3-1 and #BC.4-3-0, and Q1 covers the r16 findings.
- Part a grew from 16,479 to 16,888 characters, under 25k. The growth is the converse in #BC.3-1-3-1, which is new content.
- The definition check gives 0 conflicts. No new symbol or constant was introduced.
- The waiting specs carry BC feeaabbb7d6c and LFR2 2c5cda85d782, and all four --check runs give 0 conflicts.
- No known weak point remains, so I am launching the full round r17.

## Verdict: bp-crit-bc38a-20261108-r17

r17 was the full round of #BC.3–#BC.4-6-1 on BC feeaabbb7d6c. It found 0 fatal, 0 serious and 1 minor problem, and every r16 finding is confirmed repaired. The round is not clean, so part a's count stays 0.

Repairs (BC 71134f6166e7):
- #BC.3-1-3: "Λ₀ standing for the bonds with an end-point in it (p.277 l.17)" would also make the bonds from Λ₀ into Ω₁ data, contrary to #BC.3-1. The line now applies p.277 l.17 only to a bond ⟨a, b⟩ with a ∈ Ω₀ and b ∉ Ω₀. Such an a lies in Λ₀ by VAR (1), so VAR (3) at j = 0 makes the bond a data bond. #BC.3-1 excludes the bonds from Λ_j into (Ω_{j+1})^{(j)} because REG's cases (1.30)–(1.31) join two points of Λ_j, or a point of Λ_j and one of Λ_{j−1} (REG p.081 l.33–35). These cases say nothing of the bonds leaving Ω₀.
- New #BC.3-1-3-0, the referee's optional point: Theorem 1's uniqueness needs these data. Take b ∉ Ω₀ with neighbours a₁, a₂ ∈ Λ₀. Then U(a₁, b)U(b, a₂) is (4)-invariant, and A of (5) does not depend on it, since (5) sums over the p ⊂ Ω₀, which have all four corners in Ω₀ (p.278 l.39). Without these data, a small variation of the invariant stays in the open conditions (2) and would give distinct critical orbits.
- The u(b) = 1 argument moved to the head of #BC.3-1-3-1.

Recheck 1: #BC.3-1, #BC.3-1-3, #BC.3-1-3-0 and #BC.3-1-3-1 were reread against VAR p.277 l.11–24 and p.278 l.1–46. That covers (1)–(7), the bond identification of l.17 and the meaning of ⊂ at l.39. The re-derivations:
- a ∈ Ω₀∖Ω₁ = Λ₀, as (L⁰η)^{−1}dist(Ω₀^c, Ω₁) > RM₁ ≥ 1.
- The invariance of the product follows from u(a_i) = 1 (#T10.23).
- At the varied point, the derivative of A along the other bonds is unchanged and is 0 along the free bonds. The tangent space of 𝔙 is the product, so the point is critical.

Recheck 2: every citation of #BC.3-1-3 was grepped in BC, LFR2 and the table: #BC.3-1, #BC.4-6-1, #BC.8-5-2-0-1, #BC.8-5-2-0-2 and LFR2 #160.4-3-3. Each still points to the same content. All lines are ≤ 600 characters.

## Pre-check: bp-crit-bc38a-20261108-r18

- spec_bc38a_r18 is at BC 71134f6166e7 and LF d89bf93c0fa0. The step list adds #BC.3-1-3-0, and Q1 covers the r17 finding.
- Part a grew from 16,888 to 17,573 characters, under 25k. The growth is #BC.3-1-3-0, which is new content the referee asked for.
- No new symbol or constant was introduced. The definition check gives 0 conflicts.
- The waiting specs (bc38b r15, BC.2 r4) carry BC 71134f6166e7, and LFR2 r1 carries 2c5cda85d782. All four --check runs give 0 conflicts.
- No known weak point remains, so I am launching the full round r18.

Handover 14:21 (8 Nov): bc38a r18 is running on BC 71134f6166e7. Part a's count is 0. Still waiting: bc38b r15 (full), BC.2 r4 (full) and LFR2 r1, one at a time. The fork has been sent BC 71134f6166e7 and #BC.3-1-3-0.

## Part b read in full while bc38a r18 runs (14:3x, 8 Nov)

Every line of #BC.5–#BC.8-5-2-1 was reread before bc38b's full round r15, and each bound was re-derived. Two repairs (BC df57cd14d4a3, outside part a's reviewed lines):
- #BC.8-2-1-1 applies #BC.5-1-3-1–#BC.5-1-3-1-3 with t^X in place of Lt(B). Under that substitution, #BC.5-1-3-1-2-1's |A|₂ ≤ ½ρ₀(L^lη)^{−1} needs 2√Nt^X ≤ ρ₀, the analogue of #BC.5-1-3's 2√NLt(B) ≤ ρ₀. #BC.5-1-4 had √Nt^X ≤ ρ₀. Both #BC.5-1-4 and #BC.8-2-1-1 now read 2√Nt^X ≤ ρ₀. This is still a condition on |B| only, monotone in |B|, so r_𝒱 and #BC.8-5-2 are unaffected. BD's Step 6 itself needs only |X| ≤ ρ₀(L^jη)^{−1} (#BD.9, #BD.6, #BD.13).
- #BC.6: REG p.077 l.48's identity is stated for gauge transformations, while w is G^c-valued. The line now says that the product around p_{μν}(x) telescopes for any u with invertible values.

Re-derived without change:
- the Schwarz bound (#BC.5-1-2), t(B) = (2B₅/C₁)|B|;
- the local-gauge and A₀, A bounds (#BC.5-1-3-1-1), |b′₋ − b₋|α₀ ≤ ½(d + 2)L²B₃ε₁;
- 2dL𝔞_j ≤ 4d√NLt(B), as j < n;
- Σ_{j<n}dL𝔞_j ≤ 3d√NLt(B), as L ≥ 3;
- |B^X| ≤ 2·2(6d + 2)√NLt(B) = C_{BX}Lt(B);
- the ψ bound 2ρ₀L^{−n} (#BC.5-1-3-4-1-1);
- the path independence and F = U_L^w (#BC.5-3–#BC.5-3-1);
- the room conversions (#BC.6-1-1, #BC.7-2–#BC.7-2-1);
- the distances 3L^nη of #BC.8-2-2-1, and Ω^X_{n−1} by R′M′ ≥ 3dL;
- Θ ≤ e^{24d√Nt^X + d(t(B) + t^X)} (#BC.8-4);
- the Lie product bound and |B| ≤ 8r^{ext}_k (#BC.8-5-1).

Part b is 23,271 characters, under 25k. All lines are ≤ 600 characters. spec_bc38b_r15 and spec_bc2_r4 now carry BC df57cd14d4a3.

## #BC.2 read in full before BC.2 r4

Every line of #BC.2–#BC.2-6-1 was reread and re-derived. Checked:
- (C), with points of T^{(i)} off the faces;
- #BC.2-1-3's characterisation of Γ_n;
- (G);
- (S), including the two-touch distance 2(M₁L^q − 1)η + 2η;
- #BC.2-3-3–#BC.2-3-3-1 in all three conventions;
- the maximal sequence, the strip missing Ω_{q+1}(X) by 2d < L, and the index comparison (#BC.2-4–#BC.2-4-3);
- the corner chain (#BC.2-5–#BC.2-5-4);
- #BC.2-6–#BC.2-6-1.

Two repairs (BC 7a2af124cfa2):
- (G): "no point of Δ″ lies in Ω_{h+1}" now reads "no point of T_η in Δ″", as (C) states it.
- #BC.2-3-2: the sentence on ∂X ⊂ Ω_p applied #BC.2-5 at q = p without its hypothesis p ≤ m. It now cites #BC.2-3-3 for non-empty ∂X. For empty ∂X, X = T_η, as X is non-empty and T_η connected, and S^p_X = ∅.

#BC.2 is 9,505 characters. spec_bc38b_r15 and spec_bc2_r4 now carry 7a2af124cfa2, and the BC.2 spec's Q1 names the new check.

## LFR2 read in full before lfr2 r1 (14:27, 8 Nov)

Every line of #160.0–#160.8-2 was reread, and the following were re-derived:
- ∂(e^{iηℋ^♭}U) = aU(∂p)b, giving |∂U^♭ − 1| ≤ |∂U − 1| + |ab − 1| (#160.3-2);
- ε₀^♭ on Ω_k (#160.4);
- the index-0 data of 𝔹_k(Z) and A^η − A^Z (#160.4-2);
- ε₀ = B₃(1 + 4C₁)ε₁ in p.281 l.19 against (173), and the rooms B₃a₁η² ≤ B₃a₁η²(L^jη)^{−2}, (L^jη)^{−3} (#160.4-3);
- the partial sums 2(d − 1)B₃a₁η < B₃a₁η^{−1}, as 2(d − 1)L^{−2} < 1 (#160.4-3-1);
- the local minimum through #BC.3-6 (#160.4-3-2);
- Theorem 1's hypotheses ε₁^♭ ≤ a₁ and B₃ε₁^♭ ≤ ε₀ ≤ a₀ (#160.4-3-3);
- R(w(c₋))B^♭(c) under block-constant w (#160.6);
- the composite G and 𝐇′ through #41.1 (#160.8);
- |log ab| ≤ |log a| + |log b| through the bi-invariant distance, d_G(1, e^{iH}) = |H| for H ∈ 𝔤 near 0 (#160.8-2);
- the final constant (32dKM₀ + 1)ε_k.

One repair (LFR2 e34d620e0259): in #160.5, the trailing "(#160.6)" stood after the (7) clause. The sentence now says that B^♭ lies in the ball (172) for g small (#160.6), and that U^♭'s data satisfy (7) at ε₁, as ε₁^♭ ≤ ε₁ (#160.4-0).

spec_lfr2_r1 carries e34d620e0259. The three waiting specs give 0 conflicts in --check.

14:30 (8 Nov): the fork reports table 96401ec177ae, LABELS 9282d5618c57 and LF 16ba68a9c7f3, verified by sha256. The only row change is #T12.7-18, which adds the Cauchy note's local y. No BC or LFR2 line cites that row. The three waiting specs now carry lf_sha 16ba68a9c7f3 and give 0 conflicts in --check. bc38a r18 had been built on the earlier snapshot.

## Verdict: bp-crit-bc38a-20261108-r18

r18 was the full round of #BC.3–#BC.4-6-1 on BC 71134f6166e7. It found 0 fatal, 0 serious and 2 minor problems, both clarity points; every step was judged correct. The round is not clean, so part a's count stays 0.

Repairs (BC b49415909f78):
- #BC.3-1-3, "REG's cases say nothing of the bonds leaving Ω₀": REG p.081 l.35 is printed for every j, so as an exhaustive list it would exclude the outer bonds as well. I checked the referee's suggested source against the print. CRE p.255 l.20–21 says that (2.2), the formula of VAR's Λ_j at p.277 l.21, "is meant for sets of points, bonds and plaquettes" with RG I's convention, p.251 l.26–28: a union of cubes determines the bonds which intersect it.
  - #BC.3-1-3 now cites both lines and proves that an n-bond meets a union of n-cubes exactly when an end-point lies in it. Each point of the bond lies in no n-cube other than the two centred at its end-points, because its other points are interior to them and its midpoint is the centre of their common face; such a cube lies in the union exactly when its centre does, by (C).
  - #BC.3-1-3-0: so these are VAR's bonds of p.277 l.17. The bonds of Λ_n are the n-bonds with an end-point in Ω_n and none in Ω_{n+1}, which is exactly #BC.3-1's list. REG's case list is no longer invoked for the outer bonds.
- #BC.3-1-3-0, now #BC.3-1-3-0-1–#BC.3-1-3-0-3: the argument now states both missing points.
  - The variation stays in 𝔙. Without the outer data, the index-0 data are values at other bonds. A datum of index n ≥ 1 depends only on bonds with both end-points in Δ(c₋) ∪ Δ(c₊), by #BC.3-2 iterated over the nested levels. These points are within (1 + d/2)L^nη < R′M′L^{n−1}η of Ω_n, hence in Ω_{n−1} ⊂ Ω₀.
  - The varied configurations stay critical. (6) contains a product neighbourhood, A does not depend on the free factor, and along the other factor the derivative equals its value at the critical point, 0.
- Consequences:
  - #BC.3-1-3-1 lost its definition of ⟨a, b⟩, which stood in the old #BC.3-1-3, and now defines it, with a ∈ Λ₀ by VAR (1).
  - #BC.8-5-2-0-1 now cites #BC.3-1-3-1 for the subgroup.
  - #BC.4-4-0's closing clause covered applying l.17 to the point set Λ_j, a reading that #BC.3-1-3 now excludes from print. The clause is deleted; this changes no mathematics, as the bound on U at those p′ is still proved.

Recheck 1: the six changed lines were reread against CRE p.255 l.10–22, RG I p.251 l.24–29, VAR p.277 l.11–24 and p.278 l.1–46, and REG p.081 l.32–36. The re-derivations:
- the bond and cube incidence, with nesting at n = 0 through 0-cubes with corners at ηZ^d;
- the other end-point in Λ_{n−1}, by (1) as in #BC.3-1-2;
- the dependence of the data on fine bonds, by the nested (n−1)-cubes;
- (1 + d/2) < 3d ≤ R′M′/L;
- the product neighbourhood within (3);
- the zero derivative.

Fixed during recheck 1:
- (C) gives only "cube ⊂ union iff centre in the union", so the no-other-cube fact is now stated separately.
- "The other data of index 0 … in Λ₀" ignored the other outer bonds; it now reads "the values at other bonds".
- "Unchanged" now reads "equals its value at the critical configuration, 0".
- The out-of-order tag #BC.3-1-3-1-0 was renumbered.

Recheck 2: every citation of #BC.3-1-3, #BC.3-1-3-0, #BC.3-1-3-1 and #BC.4-4-0 was grepped in BC, LFR2, the table and the two-loops note.
- #BC.3-1 and #T12.27-1-2 cite #BC.3-1-3 as the source of the outer clause, which it still is.
- #BC.4-6-1, #BC.8-5-2-0-2 and LFR2 #160.4-3-3 cite the range #BC.3-1-3–#BC.3-1-3-1, which still covers the same content.
- No external line cites #BC.3-1-3-0 or #BC.4-4-0.
- Every line is ≤ 600 characters except #BC.3-1-3, at 623.

## Pre-check: bp-crit-bc38a-20261108-r19

- spec_bc38a_r19 is at BC b49415909f78 and LF 16ba68a9c7f3. The step list adds #BC.3-1-3-0-1–#BC.3-1-3-0-3, the claim states the CRE and RG I source, and Q1 covers the r18 findings.
- Part a grew from 17,573 to 18,922 characters, under 25k. The growth is the incidence proof and the two completed points of the uniqueness argument, which is new mathematics the referee asked for. It is partly offset by the deletion in #BC.4-4-0.
- No new symbol was introduced, and the definition check gives 0 conflicts.
- The waiting specs carry BC b49415909f78, and all four --check runs give 0 conflicts.
- No known weak point remains, so I am launching the full round r19.

14:36 (8 Nov): the fork reports table c8c0a2f0fb4a, verified by sha256, and LABELS 64375557fe73, with LF unchanged at 16ba68a9c7f3. #T12.7-18 now lists Cauchy §8.6's local B′. LFR2 uses LFR II's B′ of (1.34), V_k′ = exp ig_kB′ (#160.2-1, p.365 l.13), and does not define it; the lfr2 --check gives 0 conflicts. No spec change is needed, since the specs pin the LF, and r19 reads its own snapshot.

14:36 (8 Nov): the fork reports table 2fa4ca5e9d58, verified by sha256, and LABELS f0d7e04bb650, with LF 16ba68a9c7f3. #T12.27-1-2 was re-read in full against #BC.3-1 and #BC.3-1-3–#BC.3-1-3-0, and it matches them:
- the outer clause is sourced from CRE p.255 l.20–21 with RG I p.251 l.26–28;
- the REG pin p.081 l.33–35 is kept for the two cases inside Ω₀;
- none of the renumbered tags are cited.
No change is needed on my side.

14:47 (8 Nov): the consolidation move of the two-loops note. The user's instruction was "Just move them" (and "Don't delete them!"). The scripted exact move, approved by the user, carried the derivations byte for byte, with every tag unchanged:
- #3.2.1–#3.2.3 to balaban_proofs/BP_TL_NSTEP_FRAME.md (af74c38dbf62);
- #5.1–#5.10.6 to BP_TL_MIXED_TERM.md;
- #6.1–#6.17.3 to BP_TL_GC_TRANSFORMS.md (5f4b8aae5de9);
- #8–#218 to BP_TL_EVAL_POINTS.md.

The note went from 501,471 to 225,861 characters and keeps the statements #3.2, #5, #6, #7, and the new pointer #3.1-1 (96d81de38e42). The script checked that the kept lines and the moved lines reassemble the original.
- labels_two_loops.py now reads the note and the four files as one tag set. LABELS_TWO_LOOPS.md (ef13718683ce) gives each tag's file; all 1,155 tags are unique and every reference resolves.
- Re-pointed across files:
  - #5.6's "the restriction by χ_{h,1/2} stated above" now says "stated in #5" (BP_TL_MIXED_TERM.md 72972353027b).
  - #78's "(#220 below)" and #83's "(#220 below, #222)" lost "below" (BP_TL_EVAL_POINTS.md e974d6cb92c0).
  - Every other "above" and "below" in the four files points within its own file, or is an inequality.
- The fork and the session "yang mills 4 handover (4)" were told of the move.

14:51 (8 Nov): verdict on r19 (bc38a part a, full round): no fatal or serious finding, and two minor ones. Clean count 0.

| Finding | Repair |
|---|---|
| #BC.3-1-3-0 (minor): why (2.2) is the difference of bond sets, not the bonds of the point set Λ_n | #BC.3-1-3-0 now states that VAR's Λ_n = Ω_n^{(n)}∖Ω_{n+1}^{(n)} (p.277 l.21) is the difference of the sets of n-bonds of Ω_n and of Ω_{n+1}, not the n-bonds with an end-point in the point set Λ_n, which contains those into Ω_{n+1} |
| #BC.4-4 (minor): plaquettes read by the point set, bonds by the difference | #BC.3-1-3's lemma now covers n-plaquettes (a corner in the union; RG I p.251 l.27 names plaquettes). #BC.4-4 identifies (7)'s p′ ∈ Λ^X_j (p.278 l.39) as the j-plaquettes with a corner in Ω^X_j and none in Ω^X_{j+1}, and bounds the larger set with a corner in Λ^X_j. #BC.4-4-0 separates the two excluded kinds of bond: a corner in Ω^X_{j+1} removes p′ from Λ^X_j, and at j = 0 a bond with both end-points outside X leaves the product unformed |

Recheck 1:
- #BC.3-1-3's new proof: a point of the bond or plaquette lies in an n-cube of the union. The centre of that cube agrees with the point off its directions, since distinct lattice values differ by L^nη > ½L^nη. Along its directions the centre is one of the two values bracketing the point, so it is an end-point or a corner. Conversely, an end-point or corner is a point of the bond or plaquette. (C) is no longer needed here.
- Ω^X_j and Ω^X_{j+1} are unions of L^jη-cubes, by #BC.3-1-1 (M′L^nη-cubes with M′ a power of L).
- Consumers of #BC.3-1-3 (#BC.3-1, #BC.4-6-1, #BC.8-5-2-0-2) use only the bond statement, which is unchanged.

Recheck 2:
- The four lines were re-read in full.
- A corner in Ω^X_j∖Ω^X_{j+1} is a point of Λ^X_j by (C), so the larger set contains (7)'s p′.
- An end-point in (Ω^X_{j+1})^{(j)} is a corner of p′ in Ω^X_{j+1}.
- Lengths: #BC.3-1-3 is 642 characters, #BC.4-4 623, #BC.3-1-3-0 560, #BC.4-4-0 547.
- BC is now 89b36ba367c2.

Pre-check for r20 (full round of part a):
- Spec spec_bc38a_r20.json: BC 89b36ba367c2, LF 62701df01e9d. The caller now points to BP_TL_EVAL_POINTS.md #94 and BP_TL_GC_TRANSFORMS.md #6.16.3-2-1, and Q1 covers the r19 repairs.
- Part a grew by about 400 characters, from the plaquette identification the referee asked for, and stays under 25k. No new symbol was introduced.
- The definition check gives 0 conflicts with the BP_TL files now in balaban_proofs/.
- No known weak point remains, so I am launching r20.

14:53 (8 Nov): r20 was launched (background byx8lch4i). Bookkeeping after the move follows; no bound changes.
- BC's header (line 3) and LFR2's header now say their two-loops consumers are in BP_TL_GC_TRANSFORMS.md and BP_TL_EVAL_POINTS.md, and that a cited #x is in the note or a BP_TL file, as listed in LABELS_TWO_LOOPS.md. BC is now 50bd7fc1dc5d and LFR2 5b44c59498b9. r20 reviews BC 89b36ba367c2, which differs only in line 3, outside its extracts.
- Specs updated to LF 62701df01e9d:
  - spec_bc38b_r15: BC 50bd7fc1dc5d. The caller points to the BP_TL files, and sources_extra names them as context.
  - spec_bc2_r4: BC 50bd7fc1dc5d.
  - spec_lfr2_r1: LFR2 5b44c59498b9. The caller and sources_extra point to BP_TL_EVAL_POINTS.md, BP_TL_MIXED_TERM.md and BP_TL_GC_TRANSFORMS.md, which hold the cited tags #5.3, #5.6, #6.13, #41–#213.
- All three --check runs give 0 conflicts.

15:09 (8 Nov): bp-crit-bc38a r20 verdict (full round of part a, BC 89b36ba367c2). There are no fatal or serious findings, but three minor and two cosmetic findings, so the round is not clean and the clean count stays 0. Both r19 findings are confirmed repaired.

| Finding | Repair |
|---|---|
| #BC.4-3 and #BC.4-6: restricting (2) to the plaquettes where U⌈X(∂p) is defined is unmarked | #BC.4-3 states that VAR prints (2) for every p, b ∈ Ω_j (p.278 l.5–6), that (2) is no condition at a plaquette with a bond outside X̂, and that VAR does not state (2) at these p and b, so both conventions are this file's; #BC.4-6 names both halves |
| #BC.3-1-3-0-1: the need for data at bonds leaving Ω₀ is shown only when some b ∉ Ω₀ has two neighbours in Λ₀ | The first sentence states this condition, names the inner corner of an L-shaped Ω₀ = X, and says one convention serves all determining sets, so that case decides it; u(a_i) = 1 by a_i ∈ Λ₀ ⊂ 𝔅_k (p.278 l.18) is now written out |
| #BC.4-4: RG I (0.9) alone does not give the G-valuedness of (0.4) and (0.12) | New #BC.1-4-1-0 and #BC.1-4-1-0-1 derive it from (0.4) and (0.12) (p.253 l.5–6, p.254 l.4), with (0.9) and (0.11) (p.253 l.30, l.46) for the contour variables, either orientation of U(x′, c₊), the local inverse of A ↦ e^{iA} at 1 for the compact G ⊂ U(N) (#BC.1-0), and CMP98 p.020 l.30; #BC.4-4 cites #BC.1-4-1-0 |
| Cosmetic: 3η in #BC.4-3-1 | Now 2η |
| Cosmetic: Hermitian as an attribute of a norm in #BC.4-1-2 | Now the norm of the inner product Tr Z*Y |

Recheck 1 re-read every repaired line (#BC.1-4-1-0, #BC.3-1-3-0-1, #BC.4-1-2, #BC.4-3, #BC.4-3-1, #BC.4-4, #BC.4-6).

Recheck 2 re-read the same lines against the print: RG I p.253 l.1–8, l.26–52, p.254 l.1–7; CMP98 p.020 l.28–32; VAR p.277 l.15–22, p.278 l.1–46; CRE p.255 l.12–22; RG I p.251 l.24–29. All pins match. It found and repaired four more points:
- #BC.1-4-1-0 omitted the local-inverse step and the orientation of U(x′, c₊). Both are now written, and the line is split into #BC.1-4-1-0 and #BC.1-4-1-0-1 (349 and 356 characters).
- #BC.5-1-3-4-1-2 and #BC.5-1-3-4-2 use the same fact. They cited G = e^{i𝔤} alone and now cite #BC.1-4-1-0-1.
- #BC.4-3 and #BC.4-6 used "read" and "readings" for this file's conventions. They now say "taken" and "conventions".
- #BC.4-3 was trimmed to under 600 characters.

Uses of the touched claims were grepped:
- (2)'s convention at #BC.4-5, #BC.4-5-2-1 and #BC.4-6-0, and at LFR2 #160.4-2's line ("convention and room of BP #BC.4-3–#BC.4-3-2"), is consistent.
- G-valuedness: no other use relies on (0.9) alone.
- #BC.4-4-0's cases were re-derived; they are exhaustive.

BC is now 6d673a14154d.

Bookkeeping (no bound changes):
- BP_TL_EVAL_POINTS.md #88.1-3 cites #T4.32-1 for B̄_G (fork's request).
- BP_TL_NSTEP_FRAME.md #3.2.2-3 cites B̄_G and C_u of #T4.32-1 instead of defining them.
- BP_TL_EVAL_POINTS.md #98 cites #T4.32's bound on d_{n+1} and its S_L instead of defining S_L.
- None of the two-loops files uses #T12.9's c_q, which the fork changed from 8d to 4d (table 03d67e30244f, LF 69a55acccf73).
- EVAL is ba868ef13dab, NSTEP e855d08d2804, and LABELS_TWO_LOOPS.md 433670ba51b5 (1,159 tags).

Rewrite edits since the move, not yet refereed:
- BP_TL_NSTEP_FRAME.md #3.2.2 is now #3.2.2–#3.2.2-4 (the every-point bound on ũ_m), and #3.2.3 is deleted.
- #116.1 now cites #3.2.2–#3.2.2-4.
- #92's and #123's restatements of #123's bound are removed.
- #3.2's end, #88.1-3-1, #6.13-1 and #5.6 are re-pointed.
- These go to a referee round before part a's r21 builds on them.

Paused at the user's request: r21 is not launched. Before it, bc38b r15, BC.2 r4 and LFR2 r1 need spec SHAs updated (BC 6d673a14154d, LF 69a55acccf73).
- Message to the fork (15:12): the re-point and the two row citations are done. #T4.32-1's "uses" column should read #3.2.2-0–#3.2.2-4, #3.2.2.1, because the every-point bound and the summed second parts are #3.2.2-4.
- The fork fixed the pointer (table 6e2546085b72, LABELS 2e561549cf21, LF a63f7525078d). The specs' LF SHA is now a63f7525078d.
- Re-derived the fork's C_u check. C_uLC_GS_L covers the A_L part 4dO(1)LC_GS_L·L^Jηε_{m+1} and w_m's part 4dC_GL^Jηε_{m+1} ≤ 4dLC_GS_L·L^Jηε_{m+1} together only if C_u ≥ 4d(O(1) + 1). The fork's 4d·max(O(1), 1) is off by at most a factor 2, which #3.2.2-3's O(B̄_G) absorbs, so no bound changes. I messaged the fork about the row's wording.
- The fork corrected #T4.32-1 to C_u ≥ 4d(O(1) + 1), covering the sum (table 26aae3923b71, LABELS b3e1c969f605, LF eefa409fbeb5). The specs' LF SHA is now eefa409fbeb5.
- Re-read #T11.19 after its (0.12) widening. #BC.3-1's citation (invariance under u = 1 at the points of 𝔅_k, REG (1.14)) still holds, and its "unit bonds from Λ₀ into a coarser layer are not data" agrees with #BC.3-1.
- The row's U(x′, c₊) = U(c₊, x′)^{−1} is marked inferred. #BC.1-4-1-0 holds under either orientation, so it does not rely on it.
- No two-loops file cites #T12.13, #T12.9 or #T12.12.
- The fork changed only #T2.11-1 (table 37a392becc2e, LABELS 6518968033bf, LF unchanged at eefa409fbeb5). No two-loops file cites #T2.11-1.
- The fork changed #T12.13's M^k clause and a CRE p.243 pin (table 15ccb10dcab0, LABELS 1402be458a35). This prompted a check of #BC.1-4-1's pins against the print. CRE p.243 l.23–24 gives only the one-step average, (0.4) or (0.12) of [I], and #T10.23 is the linearisation. Neither gives the iteration, which is CMP98 (43), p.024 l.2–7.
- Bookkeeping: the CRE pin now sits next to "(0.4) or (0.12)", the iteration clause cites CMP98 p.024 l.2–7, and the #T10.23 citation is dropped. BC is now 872a7a139ba0.
- The fork made LF-only changes to #T12.9 and #T12.12 (table 539f2171b112, LABELS be49a14ae851, LF 6c8ce7f8307d). No two-loops file cites either row. The specs' LF SHA is now 6c8ce7f8307d.
- The fork applied BETA's R79m batch (table 333c91f65f8b, LABELS 62a3d94f51ee, LF 574b3d4aba22). No two-loops file cites the changed or new rows.
- 2026-11-08 15:56, bookkeeping cleanup (user: "Kill all the unnecessary bookkeeping like status remarks, hedging, old routes etc. I want only maths"). No bound changes, so no round is needed.
  - Removed from all eight files: status marks ("derived, not reviewed", "not yet reviewed", "(derived)", packet and clearance marks), file history (PRETAG, line counts, SHAs in prose), and dead routes (TL #6's reduction, MT #5.11's, EVAL #14's former covariance condition).
  - Kept: the external premises, as citations (D2.7 item 15.8's post-R base-point clause, LF's (KW), the inherited map inputs); the open-item statements (TL #941, section (9)); and "(quoted, with the bound on s_Z derived)" in EVAL #47, which marks what the print supplies.
  - Deleted lines: TL #232, TL #272 and MT #5.2. Nothing cited them. New line: MT #5.3-1.
  - The heading "*The consumers of the gradient and current conditions*" (EVAL #56) is renamed "*Where the gradient and current conditions enter*" at every citation: TL #228, TL #493 and EVAL #82.
  - Other "consumers" wording reworded in TL #227, EVAL #28, #52.1, #53 and MT #5.8.
  - Map citations by line number are re-pointed to tags:
    - the layer decay of 𝐇 → #MD2.2.6.142-19, #MD2.2.6.143-1 (EVAL #17, #130.18, #130.19, #137; GC #6.14-1, #6.16.3-0-1);
    - its inputs → #MD2.2.6.142-3 (EVAL #17);
    - p ≤ j → #MD2.2.6.142-11 (EVAL #130.15.2);
    - α_{1,j+1} ≤ (1+β₀)α_{1,j} → #MD2.2.4.72-2–#MD2.2.4.72-4, which derive it from CRE (2.6) with no further input (EVAL #53).
  - EVAL #17's clause on map l.738's accepted readings ("the map owner's to resolve") is removed.
  - Checks: labels_two_loops.py gives 1,157 tags (1,159 − 3 + 1). Every tag cited in the eight files is defined. The 48 LF tags they cite all exist in LF a8276c03efaa, and their lines match the lf-p13b2-r30 snapshot (d57736f994e7).
  - CRE p.243 l.23–24 is re-read. "The averaging operation is defined by the formula (0.4), or (0.12) in [I]" spans l.23–24, so #BC.1-4-1's pin stands. The fork's l.24–25 pin is for the clause after it.
  - SHAs: TL 2fd6fb2d0f6f (235,893 B), pair note 983efaecbd18 (87,366), NSTEP 6d7476e22668 (11,876), EVAL ad707d62dd03 (210,501), MT 5abed40329e7 (28,531), GC fadd5fb3f03e (36,374), BC 6d8ca16b97dd (63,104), LFR2 5d36fe138e4f (13,788), LABELS_TWO_LOOPS 62bde6b5c842.
- 2026-11-08 16:01: the fork reports LF packet 35's table changes: #T12.12 (C_r → C_resp, μ_mem defined once), #T12.9-1 (C_{rF} added) and #T12.17 (D2's C₁′ → C₁^{L1}). Table 1ae587c1825b and LABELS 0dc9667e8a65 are verified.
  - No two-loops file cites #T12.12, #T12.9, #T12.17, C_r, C_resp, μ_mem, C_{rF} or C₁′.
  - The LF is now 79d34350785c (the fork reported 5f8eadf33e2b). The 48 LF tags the two-loops files cite all exist there, and their lines are unchanged. The specs' LF SHA becomes 79d34350785c at the next build.
- 2026-11-08 16:12, consolidation, first pass (the "Move, then rewrite" plan; user: "Have you done the consolidation as well?").
  - EVAL roadmap deleted: #8–#12 ("How it holds", summarising #102, #124–#130.19, #138, #145, #152, #155), #18–#34 (the item list), #35–#37 ("Where it enters"), and #214–#218 (why U_k^0 itself does not do, a dead route).
  - #17 is now the inputs line only. #38 is reduced to its source (LFR I (1.89), p.197–200; LFR II p.375 l.24–27, re-read). #213 is reduced to the conclusion.
  - K is cited by table #T4.48 (EVAL #130.12.1, #167-1), not by the deleted #8. P is defined in the body (EVAL line 31) and in the table.
  - EVAL #165 now cites #45's Cauchy estimate instead of restating it. T₂ and κ are defined once, in #165.
  - TL: the framing lines #221, #235, #242 and #275 ("The issue") and #236 and #276 ("How it holds") are deleted. #222 is retitled *The domains of the clause*, and its roadmap sentence is dropped.
  - TL #228 restated the cross carry lemma's proof (#492–#496.1). It is deleted, and its two extra points moved into the proof: the conjugation factor into #493, and c̄ = c̄_* on the family (by #226's KP condition) into #494. Its citations are re-pointed: #492, #496.1, and EVAL #58 (→ #493).
  - TL #281's roadmap sentence is dropped.
  - Kept: TL #277–#279 and #237–#239, since #279's mass normalisation and #278's wrap rule are stated nowhere else, and the pair note cites them.
  - Checks: labels 1,157 → 1,132 (the 25 EVAL head tags) → 1,120 (the 5 EVAL tail tags and the 7 TL tags). Every cited tag is defined. Every TL #3/#788 input list still names existing tags.
  - SHAs: TL 8abc94d7fd91 (232,983), EVAL cfdbd980551d (192,210), LABELS_TWO_LOOPS d2470534910f. The eight files total 666,232 characters.
  - These are content edits, so the touched parts (EVAL head, TL #220–#281, #492–#496.1) go back through the referee.
- 2026-11-08 16:32 GMT, second consolidation pass (no round).
  - Peer packets 36–41 logged: the table went 1ae587c1825b → 0b911f194448 → 5cf1e503cbca → 6cffb73978ff, and LABELS → 133ab4a6e8d6 (LF 7b6bb0921595). No row of mine changed, and the cited LF tags are intact.
  - EVAL: the phase, gradient and current chains are one induction in the norms x^ν_n, ν = 0, 1, 2 (#117-1, #120–#120-2, #121–#123). #140–#144 and #148–#150 are deleted. τ_N := C_*L^NN^{2+β₀}δ′_kS_L² is new (no clash with GC's Θ or the table's τ_k), and it is local, so no table row is needed. #122 and #123 are split (#122-1, #123-1, #123-2). This saved about 0.8k, because the chains were already written as differences from the phase.
  - Headings: status parentheticals are dropped from TL (1), (4)–(7) and the pair note's §§2–7.
  - TL (6B)/(6C):
    - *The payment* (#723–#727) runs once at (5/2)ν_r for every 𝐑-group, cross or on one loop. Ψ's part comes from #724 (cross) or #849-0 (one loop), and the conditions are 5·2^{d+2}ν_r ≤ c_F^× (#727, = #287), (5/2)ν_r ≤ a_V/2 (#725), and #655's 5p₀/64.
    - #802 is deleted, and #798, #801, #850 and #728.5 are re-pointed. The pair note's #PC4.8-5.3 now cites #655's 8(1.05)^dν_r ≤ κ. The fork has been asked to re-point D2.7 15.8-1(6)'s "(#802, #849)".
    - The δ block #728–#728.4 is compressed (the CRE quotation chain and the symbol index are cut to their content). Its tags are kept, because the table cites #728.1–#728.4.
    - #638.1's dependency list is deleted.
    - #613 is split into #613-1–#613-7. Its duplicated δMt_k bound is now one bound (e^{δMt_k} ≤ e^{δM}L⁴R_k²α_{1,k}^{−2} ≤ e^{δM}e^{δMR_k/512}), and #626's restatement of ℓ ≥ MR_k cites #613-3.
    - The small-member counting is stated once, at #699 (split into #699-0–#699-4), and cited from #617, #629-3, #714-1, #715, #720 and #730. #711–#712 are deleted.
    - The η(D) payment is cited as #742-1 from #744, #769, #772, #799, #844 and #858.
    - #844-2/#844-3 are one bound with a = 0.078 (single-loop) or (3/4)ϑ_k (two-loop), split at #844-2-1. The pair note's #844-3 is re-pointed.
    - #855/#856 are one bound for the diameter and span factors, split at #855-1, with R_k² ≥ 1760/ν_r covering both.
    - #617 is split at #617-1.
  - Kept, as genuinely different arguments: the (H0)–(H2) proofs for D_g (#707–#709) and D_g^× (#717–#721). A cross group's polymers are chained through spans whose bonds lie outside ℐ(g), so one connectedness argument does not serve both.
  - Checks:
    - Labels give 1,130 tags, and every cited tag is defined.
    - Re-derived: 5·2^{d+2}ν_r ≤ c_F^× implies #762's c_F^×/8 ≥ 2^{d+1}ν_r, since 5·2^{d−1} ≥ 2^{d+1}.
    - #855-1: 88n/R_k ≤ 22Σ_PD_P/R_k² ≤ (ν_r/80)Σ_PD_P under R_k² ≥ 1760/ν_r, and (21/20)σ/R_k ≤ (ν_r/16)σ under R_k ≥ 17/ν_r.
    - #844-2-1: c_r⁺ϑ_k²/(0.078eν_r) ≤ C_ϑϑ_k² and (4/3)c_r⁺ϑ_k/(eν_r) ≤ C_ϑϑ_k.
    - #613-7: Σ_{m≥1}x^m ≤ 1 at x ≤ ½.
  - SHAs: TL fe9d4bb44552 (228,548), pair note ea9bfef840e1, EVAL 2d58500529bc (191,505), LABELS_TWO_LOOPS 8939da502071.
  - The touched parts (EVAL #117–#123, TL #613–#858) lose their clean counts and go back through the referee when launches resume.
  - Fork reply: the table is now dc1cb60d689b and LABELS c3c3e1246840 (LF 4543bee08e26).
    - #T4.53: t_k cites #613-2-1, c_r and c_r⁺ cite #613-4, and C_α and δ cite (#613-2-1, #728.1).
    - #T12.2: D^{𝒦} cites #613-2, and the new entry η(D) cites #613-4, with its clash against the spacing η noted.
    - Checked: the table SHA matches, the three tags exist, and each cited definition is the one at that tag.
    - The D2.7 15.8-1(6) re-point to (#725–#727, #849) is forwarded to the LF session, which owns D2.7. Until then that citation points at a deleted tag.
    - Later fork message: (4) fixed D2.7 15.8-1(6) (D2.7 acc5473be0e0). Table d7dcfb522f48, LABELS d172651d2918; no row of mine changed.
- 2026-11-08, third consolidation pass (structural, no round).
  - D_g^× is #241's D_G with G = {g} (#246). So (6B)'s second-case copies of #241 are deleted:
    - #731 (= #264);
    - #769–#771 (= #265–#269, with y^R_k and C_y defined a second time);
    - #772, whose h(W) = ∅ sentence moves into #270.
    - #769 now applies #264–#270 at G = {g}. Re-derived: σ(D_G) at G = {g} is σ_g (c_D = ½), θ^× = θ(g), λ_k(D_G) = λ_k(D_g^×), and C_y = 77MC_lk/(eν_r) as before.
  - Head summaries are deleted:
    - #234/#237–#239 (= #698–#705);
    - #274/#277–#279 (= #836–#845; the wrap rule is #842, the normalisation #845);
    - #281 (a roadmap).
    - #3 and #793 now list #7, #220 and #241, with the single-loop (6.3)'s use pointed at #701–#705 and #836–#843.
  - #785 now cites #230 instead of re-arguing it, and #619 cites #229 (its T-step sentence is #224's and #869's).
  - Pair note re-pointed: #278 → #842 (#PC4.13-6, #PC4.14.4-4.5.4-6, -6's sibling) and #279 → #845.
  - Fork asked to re-point: the table's (#269, #770)/#771 → (#267, #269)/#769, and #234/#274 → #701–#705/#836–#845, in the table and in D2.7.
  - Checks: labels give 1,117 tags, and every cited tag is defined.
  - Fork reply: table d77bb0a78521, LABELS 5fe3ef2b548d (LF 192ea5f46f57).
    - Re-pointed: #T4.31 and #T12.2-9 → (#267, #269), #771 → #769, and #T6.21 → #701–#705/#836–#845. D2.7's l.3 and l.10 are forwarded to (4).
    - Checked: the table cites no deleted tag.
    - The C_y row's stale clause "replaces the cube count's 73C_gr/(eν_r)" is sent back for deletion, since that constant no longer exists in TL. The fork dropped it: table f12f10529d8e, LABELS 46b34f973af2. Checked: no 73C_ is left in the table or in TL.
    - Then table 64d472a204d7, LABELS a8a346116517: #T6.21 cites #836–#843-1 for the attached extent, and D2.7 (ed28e55e7e78) cites #701–#705 and #836–#843. Checked:
      - #844–#848 are under *The members' weights*, so the narrower range is right.
      - D2.7 l.10 cites the e^{17ν_r} normalisation separately, as (6C) *The members' weights*. So #279's old content is still cited, through #845.
  - SHAs: TL 2627ae6c3106 (224,163), pair note d821a40e49e2, LABELS_TWO_LOOPS 54c5d3a60686. The eight files total 656,544 characters.

## TL consolidation: arguments run once (17:07, 8 Nov)

Bookkeeping and merging only: each merged argument is the old one run once for all of its cases, and no bound changes.
- (6A)(i) *Units with a factor* is one block, #566 with #555, #568, #558, #560–#564, #569, #570, #570-1, #571, #572 and #572-1. It is stated for a general u, and the u = 1 copies are deleted: #541, #542, #556, #557, #559, #565 and #567.
  - C_win^× ≤ 196u/c_w (#568). Check: 4(24u + 1 + 24u/c_w) ≤ 196u/c_w for c_w ≤ 1.
  - #569: (8496·17/16 + 11)/(4·10⁴) ≤ 0.226, and 1408u ≤ 4096L.
- *𝐑-made insertions* #518–#525 are general, for D_g^× and D_g alike. The per-case copies #700, #700-1, #702, #704, #707, #708 and #831 are deleted, and #709 and #830 cite #518–#525.
- #540 covers a touched W. The single-interval share is dominated by the general one: 10240 ≤ 20480, 1024 ≤ 8320 and 81 ≤ 88, and the computation is monotone.
- The margin of (1.89) is one lemma, #652 with #652-1. It is cited by #645, #655, #797, #835 and #843-1, and is used once per component's X′_r and once per group.
- c_F^× := δM/2 = ½ (#636, #728.5), and the min(1, ·) case is deleted.
- Ψ_g:
  - #681–#682 serve every group: rooted at π_k-cubes of hull^×(g), at slot bonds N_sl(g), or at span bonds.
  - #724 serves every group, and #685-1 and #769 give D_g^× = D_G with G = {g}.
  - Deleted: #686–#688, #768, #849-0, #849-1, #851, #852 and #859, the coarse MR_k-cube root count. That count needed ε² = e^{−p₀/2} per cube, and #682 roots at π_k resolution, so no R_k^d arises there.
- New: #841-1 and #842-1, the register growth of a wrap or single-loop W₁ at the 𝐑-step.
- (8.2):
  - #926–#932 deleted, and #917 lists all hypotheses. N_s ≥ 2max(ℓ₁, ℓ₂) is at #290, and #920's ν_r conditions point to #287.
  - #258 deleted: #257 carries the merged share.
- Recheck pass 1, every edited line re-read, found two defects:
  - #525 named H_i(g); it now reads H_i(D), for a cross group.
  - #728.1 and #728.3 had merged into one line; they are split.
- Recheck pass 2: (6A)(i), (6B) #670–#722, (6C) #825–#844-5 and the head #241–#288 re-read, with every constant recomputed:
  - #257's 0.227;
  - #696's 0.21;
  - #698's 21M;
  - #724's 32.5 + 276M ≤ 64 + 1280M;
  - #828–#829;
  - #835;
  - #843-1's 4.03 ≤ 4.1.
  - No further defect.
- Pair note: #PC2.3's #932 → #290; #PC8.1's (#917, #932) → (#917); #PC7.2's #932 → #290.
- N-loops note (this session's derived companion), stale against TL. Repaired:
  - #NL6A.5: C_win^× in its u-form, ≤ 98N_Cu/c_w, with #568 and #558; (T0) cites #572 and #572-1.
  - #NL6A.6: the factors are u ≤ u_𝔏 for all 𝐑-made insertions (#629-5), and u₁^{(N)} ≤ 2.
  - #NL6A.9: L₀^{(N)} := (N_C/2)L₀^× in place of the stale (N_C/2)·10⁶, with the transport condition 704N_Cu_𝔏 ≤ 4096L.
  - #NL12.1 cites #NL6A.9 and drops #932.
- Checks:
  - no dangling reference in the eight files or the N-loops note, except the LF tags;
  - lines this batch rewrote that exceeded 620 characters are split at sentence boundaries: #678-1, #693-1, #693-2, #696-1, #698-1, #698-2, #706-1, #722-1–#722-3 and #728.1-1;
  - labels give 1,102 tags.
- Fork messaged, with table adc3050ab48f:
  - #T4.53: C_win^× in its u-form at #568, c_sh^× under #569, and #557 replaced by #568 and #569;
  - #T12.2-11: c_sh′ (#542) deleted;
  - #T12.2-12-1: c_F^× := δM/2 = ½;
  - D2.7 l.183: #849-0 → #811, #814-4-2-4 and #724 (via (4)).
- SHAs:
  - TL 36c80fd87aeb, 216,048 characters, down from 224,163 (018f429fde46 before the splits);
- Fork reply:
  - Applied: table 324487c939e9, LABELS 8835b7eaeffd (LF 9e8271fad2b2). D2.7 l.183 is forwarded to (4). #T4.30 now reads ν ≤ 1/(5·2^{d+3}), which agrees with #287.
  - The fork found that the count 4(24u + 1 + 24u/c_w) above drops a +1: the crude head-plus-tail bound is 24u + 2 + 24u/c_w.
  - Re-derived: the sum is 24u + θ + e^{−aθ}/(1 − e^{−a}), with a := c_w/(24u) and θ ∈ (0, 1]. It is convex in θ and equals 24u + 1 + 1/(e^a − 1) at both ends, so it is ≤ 24u + 1 + 24u/c_w, and 196u/c_w stands.
  - The computation is now in #568 itself. TL 5d71c8ff706a.
  - Then table a65e9779ef52, LABELS 42786738c9e4: #T12.2-9-1 cites #722-1 and #722-2.

## EVAL: arguments run once (17:15, 8 Nov)

Bookkeeping and merging only: each merged argument keeps its home, and no bound changes.
- The chain:
  - #156.1 is deleted, since it restated #86-0 and #86-0-1.
  - #87 cites #157–#157-3 for Ũ^{(0)c} ⊂ 𝒟^3_k, and the restated "coincides" clause is gone.
  - #86 cites #156 for where (1.65) is applied.
  - #157 now carries the acceptance of Bałaban's "almost identical" claim, moved from #158.
  - #158 keeps its conclusion and cites #6.13-0, #6.13-1, #87 and #88. The restatement of #6.13-1's f♮ argument is gone.
- Nesting:
  - *The identity on minimisers* (#130) is the one argument.
  - #133 cites it, and keeps Bałaban's printed instances RG1 (3.3) and LFR II (1.36).
  - #130.4's re-run (nesting, the 2Kh margin restated from #138, and part (b)'s representative ahead of #130.8–#130.9) is deleted.
  - #130's pointer back to *At s = 1* is deleted.
- s ≠ 1:
  - #130.1 cites #137's bound for each member's P_Ω.
  - #130.9's restated #138 inequalities are replaced by a citation.
- The current budget is one sum, in #166. #137's partial sum is deleted, and #130.4 points to #166.
- #130.18 and #130.19:
  - the bounds on 𝐇_𝐕 and the RG1 p.275 quote are stated once, in #130.19;
  - #136 cites #130.19 for the second-order terms.
- #130.12 and #130.12.1 are merged into one line, which cites #173.1–#173.7. The dead route via CRE (2.36) is deleted. #130.12 keeps g_n ≤ (1+β₀)g_k and α_{0,n} ≤ (1+β₀)α_{0,k}, which #14, #88.1-3-0 and GC #6.16.1-1/-2 cite.
- #152 and #154 cite #6.13-1 and #130.11–#130.12.2 instead of restating them.
- Checks: labels give 1,100 tags, and there are no dangling references.
- Size and SHAs: EVAL 191,505 → 187,574 characters, 373c2fcd7716; LABELS_TWO_LOOPS 7686806517ae.
  - pair note 60e68441d313;
  - N-loops 338fe73bbc37;
  - LABELS_TWO_LOOPS 105157127688.

## GC and MIXED: arguments run once (17:30, 8 Nov)
- GC, the conjugation bound: #6.2 is the one argument, giving 1 + x_n/16 once the log bound is ≤ β/32.
  - #6.13-1 cites it, and its re-run and repeated inputs are deleted.
  - EVAL #88.1-3-1 cites it ("as at #6.2"). #88.1-3 now names #6.2's inputs.
- GC, a_t's bounds:
  - stated once, in #6.14.1;
  - #6.14.2 cites #6.14.1 for a_t's bounds and (190)'s D*D entry;
  - #6.14.1 is split into #6.14.1, -1 and -2, and #6.14.2 into #6.14.2 and -1.
  - "K := O(C_dS_L)" is replaced by table #T4.48, and #6.14.2's local λ_w redefinition is deleted. The bound needs μ ≥ O(K)Lλ_R, which #52.1 gives.
- Earlier GC deletions (#6.3, #6.5; trims of #6.4, #6.9, #6.10, #6.13-2 and #6.16.5): pass 1 and pass 2 both checked, including #6.9's arithmetic.
- MIXED, contradiction repaired: #5.3 had λ absorb C_{resp,∞}·M⁵, while #5.7 has the M⁵ part as T₁'s, never passing through C_{resp,∞}. #5.3 now cites #5.7.
- MIXED, repeats removed:
  - #5.9 (REG's B₀) is merged into #5.3, with the pin corrected to p.87 l.16–17 (checked in REG parts p086, p087). #5.3-1 (summary) is deleted.
  - The contact sites are now treated once, in #5.8 (1). The tails of #5.11 and #5.10.6 cite it.
  - #5.8 (a) duplicated #5.10.5 (ii) and is deleted; the real-base passage is #5.10.5-2/-3.
  - #5.8's restatements of #5.10/#5.10.6 are deleted, including the dangling "(i) below".
  - (b) and (c) are now #5.8-1 and #5.8-2. (c)'s circular "by (c)" is split into #5.8-3.
  - #5.10's roadmap tail is deleted. #5.5's duplicated "j ≥ 1" clause is merged. #5.7's re-derivation of λ^{(k)}_n = λ now cites #166.
  - #5.1's "this real data difference" now names the difference (#5).
- MIXED, symbols:
  - ε_Q was undefined; it is now given in #5.10.5-3 from the passage draft §9 (*The cube Q_z*), with a_z (the draft's a₀; the table already has two a₀) and s_z.
  - The draft's R and M are written R′ and M′.
  - K_{CRE}, which was not a table symbol, is replaced by the table's K_{M′} (#T1.5) in MIXED and EVAL #99.
- Citers re-pointed: TL #5 now cites #5.8-2 and #5.10.5-1–#5.10.5-2. EVAL #166 now cites #5.10.5-2, #5.8-2 and #5.8-3, and its "; On" is repaired.
- λ_w := λL restatements in GC #6.2 and EVAL #166 and the two other lines are replaced by citations.
- Fork: told the table 84201f79899c (no two-loops row changed); sent T12.2-2's a_t citation, the new symbols a_z, ε_Q, s_z and Q_z, the K_{CRE} removal, and the moved tags.
- Size: GC 36,374 → 34,168; MIXED 28,531 → 26,217; EVAL 187,574 → 187,579 (net growth from the #99 table pointer and #166's added citations, partly offset by the deletions).
- Checks: labels give 1,105 tags; no dangling references.
- SHAs: GC 05e721c888ad, EVAL 3ff17b92b553, MIXED e57d8af3f1b0, TL 46e7caa6fe2c, LABELS_TWO_LOOPS 158af707172d.

## NSTEP, BC and LFR2: arguments run once (17:42, 8 Nov)
- NSTEP:
  - #3.2.1.2 (c) cites #3.2.1.1 (ii)–(iii) instead of restating the lower bounds.
  - #3.2.1.2.1's p₀ − p₁ > 1 is re-pointed to #3.2.1.1 (ii).
  - #3.2.2-3 cites B̄_G of #T4.32-1, and the unused C_u is dropped.
- BC:
  - The bare K is replaced by K_{M′} (#T1.5) at #BC.2-1-3, #BC.2-5-4, #BC.3-1-1, #BC.3-1-1-1 and #BC.3-6-1, as the bare K clashed with #T4.48's K.
  - #BC.4 now takes any G-valued U in 𝔘(𝐁, B₃ε₁) ∩ 𝔙(𝐁, V) at which A^η restricted to that space is minimal, with W := M_{𝐁^X}(U). Checked clause by clause: #BC.4-4, #BC.4-5-2 and #BC.4-6 use only this; #BC.5-2-2 and #BC.8-1 meet it through VAR Theorem 1.
  - New #BC.4-7 gives the localised sets 𝐁_k(X′) of #BC.3-6.
  - #BC.5-2-1/-2's local ε₁′ is renamed ε₁^V (it clashed with LF's {#D.ε₁′}, #T3.34-2).
- LFR2:
  - #160.4-0, #160.4-2, #160.4-3 and #160.4-3-1–#160.4-3-3 (a re-run of the #BC.4 argument at Z) are deleted.
  - #160.4-1/-1-1 now cite BP #BC.4 with #BC.4-7 at X′ = Z. The direction U(𝔹_k(Z), ·) = (U^♭⌈_Z)^w is as in #BC.4.
  - ε₁′ is renamed {#D.ε₁^♮} ε₁^♮ := (1 + 4C₁)ε₁, which removes the clash with LF's ε₁′.
  - #160.5 cites #160.4-1-1 for the VAR (7) level ε₁^Z.
- Fork:
  - Sent the ε₁^♮ and ε₁^V renames and the SHAs, for #T12.18-1 (table 86b6d6fa6264).
  - Sent, for the LF owner, the user's point that LF #4.537-1's C_L is undefined, with a derivation from LFR I p.192 l.18–19, β₀ ≤ ½, L ≥ 8 and R_k ≥ 1: N₀ + 1 ≤ 7(1 + log R_k), via log x ≤ x/e < x log L. Its consumers are #4.537-1.1 and #4.454.18-1, and the clash clauses (LF #4.454.25-1, table l.144, #T10.20) then lapse.
- Size: NSTEP 11,876 → 11,840; BC 63,104 → 63,856 (#BC.4-7); LFR2 13,788 → 11,404.
- Checks: labels give 1,105 tags; no ε₁′ is left in BC or LFR2.
- SHAs: NSTEP 2d67b6f082f3, BC 80f752c6c69a, LFR2 11b19de0717f, LABELS_TWO_LOOPS 158af707172d.

## Pair note §4: the cross and wrap insertions run once (17:50, 8 Nov)
- The old insertions:
  - #PC4.5 heads the old cross and old wrap insertions together. #PC4.11, #PC4.11.1, #PC4.12 and #PC4.12.1 are moved up beside #PC4.6.
  - "Differ by at most 2τ at every step" is now stated once per species: at #PC4.6-2 (from the old #PC4.8-9) and at #PC4.12.1.
  - The drop argument is run once at #PC4.7–#PC4.7-1 for both species, giving 2(τ^cr_K + τ^{w,×}_K)B^×_W. #PC4.12.2 is deleted.
- The young insertions:
  - The wrap births #PC4.13–#PC4.13.3 are one line, #PC4.13, citing #PC4.8-8.
  - The take-ins of old differences (the old #PC4.8-9, #PC4.9-1.2, #PC4.13-1.2 and #PC4.13-6.1) are one block, #PC4.8-9–#PC4.8-9.2: 24τ^cr_K by the young cross insertions, and 6τ^cr_K + 6τ^{w,×}_K by the young wraps.
  - #PC4.13-6 now states the passing factor 1 + 2y^R_i ≤ 3 that #PC4.14-5.1 uses. #PC4.13-6.1–#PC4.13-6.3 are deleted; 6.2 is merged into #PC4.13-6, and 6.3 restated #PC4.14-5.2.
  - D^cr_K = D^{w,×}_K := D^{cw}_K is defined once, at #PC4.10. Deleted: #PC4.8-4 (a dangling "differ by at most"), #PC4.9, #PC4.9-1, #PC4.9-1.1, #PC4.9-1.2 and #PC4.13-1.3.
  - The product-form effect of the young cross insertions and the young wraps is one statement, #PC4.10-1 (from the old #PC4.10 and #PC4.13-2).
  - #PC4.9-2 now names its terms.
  - #PC4.14-5.3 carries the per-step sources with their justification (#PC4.14-5.3-1, from the old #PC4.9-1).
- Citers re-pointed:
  - #PC4.2-2.2, #PC4.2-2.5, #PC4.4, #PC4.14-1b.5, #PC4.14-2.1, #PC4.14-5.0.1, #PC4.14-5.6, #PC6.2, #PC6.3 and #PC6.3-3;
  - the "every step" uses of #PC4.12 → #PC4.12.1 (also at #PC4.14.4-4.13.3-1, #PC4.14-1b.4.4 and #PC4.14-6.1).
- Fork: the table rows #T4.54 (#PC4.9) and #T12.3-1 (#PC4.13-1.3, #PC4.13.3) need re-pointing to #PC4.10 and #PC4.13.
- Size: 87,197 → 86,145 (wc -m). Checks: no dangling PC tags, no line over 620 characters, labels give 1,105 tags.
- Rechecks: two full passes of #PC4.5–#PC4.9-2.1 and of the re-pointed lines. They repaired "is" → "is at most" in #PC4.5, the τ wording in #PC4.7, and a doubled parenthesis in #PC4.14-5.3-1.
- SHAs: pair 018a6b07701c, LABELS_TWO_LOOPS 158af707172d.
- Fork applied the re-points: #T4.54 → #PC4.10; #T12.3-1 → #PC4.10 and #PC4.13. Every #PC tag the table cites exists at 018a6b07701c (table 0d5a4b20ef4e, LABELS ec9a74b2a081).

## TL transport conditions and EVAL #70 pins (17:53, 8 Nov)
- TL #584 was wrong. "96·19·64 ≤ 4096L" covers only u_W ≤ 19, while u_W ≤ u_𝔏 = 46080 (#583). With c_πα_{1,k+1}M ≤ ν/4096 the condition needs 96·64u_W ≤ 4096L, that is L ≥ 3u_W/2, which #583's L ≥ 8832u_W gives. Repaired in place, together with ν_f ≥ ν/16 (#MD2.4.12.21: ν_f := ν/16 + ν_r) for the 120M condition, and ν_r = ν.
- TL #543, #569 and #584 now cite the source of c_πα_{1,k+1}·4096M ≤ ν (map #MD2.4.13.19-1). #543 also cites ν_f ≥ ν/16 for its 81M condition. #569's arithmetic is checked: 9038/(4·10⁴) ≤ 0.226 ≤ ¼ and 1408u ≤ 4096L.
- EVAL #70: "SW l.103" → l.95, where SW's (6c) is (l.103 is (6e)), and the 4096 condition also cites map #MD2.4.13.19-1. Covariance note l.13, l.20, l.26–29, l.87 and l.110 and SW l.93 (in EVAL and GC) are checked against the text.
- SHAs: TL ba8498280c95, EVAL a0e672d6d405, LABELS_TWO_LOOPS 6b938600c6e2 (1,105 tags).

## TL (6C): re-derivations of Bałaban's work moved to balaban_proofs/ (18:00, 8 Nov)
- I checked the earlier offer against the text: "#803–#823, #819.1, #642–#644, #628-1-1, #629-0-x, about 25–30k".
  - Not re-derivations, kept in TL: #628-1-1 (a reading of CRE's "compatible"); #629-0–#629-0-3 (our links' data, using CRE's sets); #642–#644 (one-line consequences of RG II p.20 l.17 and LFR II p.389, p.376, and the identification of κ₁); #804 (a citation of LFR I p.177).
  - Also kept: the bulk of #800–#823, which is our two-loops mathematics (the groups, the links, the mixed Kotecký–Preiss weights and criterion, D2.7's insertions and payments).
- Re-derivations of properties and estimates of Bałaban's construction, moved verbatim to the new balaban_proofs/BP_TL_SECOND_CLASS.md:
  - #805's proof (now #805-1);
  - #812's q-split argument (now #812-0) and #812-1;
  - #814-1, #814-1-0, #814-2 and #814-2-1;
  - #814-4-2's case split (now the head of #814-4-2-0), #814-4-2-0, #814-4-2-0-1, #814-4-2-1 and #814-4-2-2;
  - #819.1.
  - In all, about 6.2k characters, not 25–30k.
- TL keeps the statements:
  - #805;
  - #812 (rewritten as statement plus pointer);
  - the new #814-0 (*The root and the count*, with κ large, #T3.34, restored from #814-2 on recheck);
  - #814-4-2 (statement plus pointer);
  - #819, which cites #819.1.
- TL #3.1-1 lists the new file; labels_two_loops.py's SATELLITES has it.
- Size: TL 216,461 → 211,390; the new file is 6,573.
- Checks: labels give 1,108 tags (new: #805-1, #812-0, #814-0); no dangling tags.
- Rechecks: two passes, comparing the statements with the moved derivations. The table rows citing #805, #812, #814-1, #814-2 and #814-4-2 resolve unchanged.
- Found, not repaired: about 40 pre-existing lines over 1,300 characters in the BP_TL files (EVAL l.154 is 7,741), against the ~600 limit.
- SHAs: TL 1986b447a035, BP_TL_SECOND_CLASS bc77a2f5e957, LABELS_TWO_LOOPS 7bc5262e2786, labels_two_loops.py 127e93a4882d.
- EVAL #107–#108: C_D → C_{D₀}, which removes the clash with the LF's age-factor C_D (#T4.29-1). The fork is asked to rename #T4.32-0 and drop its clash clause. My earlier message saying no two-loops file used C_D was wrong and has been corrected. EVAL df44fb8d44ed.
- Fork: table 23560534e7eb has #T4.32-0 as C_{D₀} citing BP_TL_EVAL_POINTS.md #107, with the clash clause dropped; the LF's age-factor constant is now C_irr (#T4.29-2); #T4.43 cites BP_TL_SECOND_CLASS.md.

## TL #628-1-1: compatibility is printed (18:07, 8 Nov)
- #628-1-1 said "CRE does not define 'compatible'; we use it … in its set sense", which was our reading, unlabelled. Bałaban prints the set sense: "compatible with the block structure of the lattice T, i.e. for every j the cube □_j is a sum of the big blocks of the lattice T_{L^{−j}}" (REG p.098 l.20–21, file lines; REG has no corrected file for p.98).
- The sentence is replaced by that quote. The CRE pins p.264 l.54–55 and p.245 l.38–39 are checked against the corrected files.
- No citer (BP #814-1) or table row depends on the old wording. The recheck moved the REG pin from l.19–20 to l.20–21.
- TL b147192706c9.

## Sweep for readings standing in for the print (18:21, 8 Nov)
Every "undefined", "not printed", "does not define/fix/say/state", "neither", "read as", "taken as" and "means" in the owned files was checked against the transcriptions. Hits about V4, the map or the notes' own objects need no source check.
- EVAL #167-1 (corrected 8 Nov, after the fork's #T3.40 message): CRE uses p₁ only at p.276 l.30 and does not define it. LFR I's p₁(g_j) = (log g_j^{−2})^{p₁}, p₁ < p₀ (p.183 l.2) is a later paper's, and it has a different form from CRE's p₀(g₀) = A₀(log g₀^{−2})^{p₀} (CRE p.244 l.22). So applying it to CRE's p₁ would be a reading. The line now says only that CRE (3.43)'s radius C₁p₁(g_k), the only p₁ in CRE, is not used.
- TL #609 and EVAL #173.6: "N read as N_k" is a choice, not a reading. LFR I leaves N to be fixed (p.177 l.31–32). Both lines now say N is taken as N_k, meeting the conditions of #3.2.1.1–#3.2.1.2.1 (the first draft's "every condition" was narrowed).
- NSTEP #3.2.1: its sentence on LFR II's N = R_j restated #3.2.1.2, which quotes p.384 l.14–17. It is replaced by "N is taken as N_k (#3.2.1.2)".
- BC #BC.4-3: "VAR does not state (2) at these p and b" is false. VAR prints (2) at every p, b ∈ Ω_j (p.278 l.5–6), with a plaquette in Ω_j when a corner is (p.277 l.17), for configurations on Ω_0 (p.278 l.2). REG's (1.7)–(1.9), which VAR recalls, are on configurations on T_η (REG p.077 l.32–40). What VAR's definition does not say is how (2) is formed where a configuration on Ω_0 does not determine it; a grep of VAR for the boundary of Ω_0 finds nothing.
  - Repair: #BC.4-3 states these print facts.
  - The plaquette convention moves into #BC.4-3-0, which now also says that every other p ∈ Ω^X_j has a corner in Ω^X_j ⊂ Ω_j (#BC.4-2). The bond convention moves into #BC.4-3-2, next to the summands it names.
  - #BC.4-5-2-1 now cites #BC.4-3-2, and #BC.4-6-0 cites #BC.4-3–#BC.4-3-2. The mathematics is unchanged.
- BP-repl header and EVAL #160-1: "prints neither the representation nor its bound" is too strong. p.365 l.35–36 says "transformed in the same way as above", which is (1.36)'s representation around U_k with the expansion of the type (1.17) (l.20–31). Only the bound on the new terms is unprinted: they enter (1.37)'s O(1) (l.43–51), and p.366 l.1–16 bounds only the (g″)^{−2} − g^{−2} term.
  - Both lines now quote this.
  - EVAL #160-1 is split at its sentence boundary; the new #160-1-1 is 456 characters.
- Checked and kept:
  - NSTEP #3.2.1.1-0's "r₀ undefined there": no transcription defines LFR II's r₀; the r₀ of BO99 and CAR are unrelated, and the line derives what the display needs with CRE's r.
  - TL #728's "inferred … not printed" on the agreement of the δ rates is labelled.
  - BC #BC.7-1-1's "J(F)(b) is not defined" concerns F on X̂, not the print.
  - NSTEP #3.2.1.1-1's L^{N₀−1} = R_{k−N₀+1} ≤ (L+1)(N₀+1)^{β₀}R_k is LFR I p.192 l.18–19 as printed.
- Rechecks: two passes over each changed line and its citers. Labels give 1,109 tags (new: #160-1-1); no dangling tags.
- SHAs: TL 13ddd13777de, EVAL 85abe8931262, NSTEP 9354bf8eb70d, BC 8c56ee00f824, BP-repl 188d84c48989, LABELS_TWO_LOOPS 5ec68647f37b.
- 18:43: EVAL #167-1's last sentence ("the radius C₁p₁(g_k) of CRE (3.43) … is not used") is deleted as an aside. #167-1 already defines the radius the notes use, r^{an}_k of 𝒫_k^{3/4}. LFR I's p₁ cannot serve as CRE's p₁: the rescaled fluctuation is integrated over |A| < r^χ_k = A₁(log g_k^{−2})^{p₀} (#T3.27, Cauchy #C8.2.1), and C₁(log g_k^{−2})^{p₁} < r^χ_k for p₁ < p₀ and g small. No two-loops file now mentions C₁p₁(g_k). EVAL 380a7cbf34ff.
- 18:53, the remaining readings in the owned files:
  - TL #643: "the identification of [I] with RG II is by" matching (I.6.34) and (I.6.41) was a reading. The print settles it: RG II prints "(6.6)" for its own (1.6) (p.3, print l.17, corrected l.16) and "(7.14)" for its own (2.14) (p.15, print l.31, corrected l.30). CRE's [I] is RG I (CMP 109; CRE p.285), which has §§0–5 only.
  - TL #728 had "that the two rates agree is inferred from this shared form, not printed"; this is now derived, in #728–#728-1.
    - The p.376 l.11–16 factor comes from the decay of the 𝐇-functions in PRT2 (2.46)'s distance. LFR II takes those functions from VAR (p.367 l.47, p.370 l.39) and their decay from VAR (190) (p.360 l.22–23).
    - (190) prints exp(−⅛δ₀d(y,y′)) (VAR p.308 l.42), in [3] = PRT2's distance (p.288 l.45), with δ₀ PBG Theorem 3.12's (VAR p.285 l.25–27, p.288 l.40–41; PBG p.423 l.39–40, "a positive, absolute constant depending on d and L only"). So δ_𝐇 is a constant of d and L, fixed before M.
    - The CRE p.251 comparison and the old p.368 (1.47) pin are deleted. #728-1 is new.
  - TL #298, the inherited input "LFR II's δ as CRE's decay rate", is deleted, as it is now derived (#728). #728.3 cites #728 in its place.
  - Not of Bałaban, kept: #297 and l.157 (the map's inherited reading of V4's step-1 factors, map #MD2.4.5.10) and N-loops §6A (the several-component reading of the map). These read our own documents.
  - Rechecks: every new pin was read in the corrected files; p.357 l.19 and p.367 l.30 were dropped from #728, since they concern the current condition and U_0's extension, not 𝐇-functions. Labels give 1,109 tags.
  - TL 85a1a34af81d, LABELS_TWO_LOOPS 9af93af4a475.

## LF Open Gaps: the one OPEN item, sent to the fork (19:20, 8 Nov)

- User: "Are there any open gaps in that LF section left?" and then "Tell this to the fork and tell it to close the gap, then review the remaining items".
- Read against the LF at 19:18.
  - #S0 has one OPEN item: #0.0, σ on 𝒟^c, also marked in the body at #4.293.4-3.
  - What is missing (#0.0-1 (a)): LFR I (1.64)(i)'s current conditions (𝕁, J_{p,X}(M^·(𝐔)), A′, ∇A′, Λ^∼; p.190 l.21–27) at U_k⁰(𝐔, t(𝐉₀ + δ)). (b) and the plaquette budgets are handled in #4.293.3–#4.293.5, and both rest on (a).
  - Everything else in #S0 (#0.1–#0.20) is derived and awaiting review. #0.16's (L-V) is a large-L condition, not a gap.
- Sent to "yang mills 4 handover (2) ⑂":
  - close #0.0 (a), with a suggested route that is not yet derived: the 𝐇-function dependence of #4.293.2-2 against the halved thresholds of (1.64)(i);
  - then review #0.1–#0.20 in packets of ≤ 25k characters;
  - before building those packets, move the derivations #0.1.2–#0.1.42 (about 80–100k) to their homes #SA–#A.17 and §4(d).
- Fork's reply:
  - It forwarded the message to (4) in full.
  - It pointed out that λ_β (#T3.34-3, #4.460-1.2) is the prefactor of LFR I (1.64)–(1.68)'s thresholds, with λ_β ≥ ½ at β = 1/8. This is a possible source of the room at 𝐉₀; it is information, not yet checked here.
  - Table 1029af23549c, LABELS 95e4bfc5a346, LF bf4760f05ca9.
- Fork, later: table 0ad9b95607a4, LABELS 277e22fa834d, LF 938987135236.
  - New rows: #T4.29-4–#T4.29-7. #T12.9 and #T12.12 are touched for 𝔰 and ϱ. (4) has #0.0 next in its queue.
  - Checked: no file of mine cites these rows or uses their symbols, except 𝔰.
  - My notes use V4's 𝔰(W), the hull size in 𝔞_W = η𝔰(W) (V4 L5249): TL #252–#255, #308, #556, #558, #737, pair #135, N-loops §§3–9. The table has no row for it.
  - Sent: proposal to add "not V4's 𝔰(W)" to the 𝔰 entries of #T12.12 and #T12.9. It is a clash note only.
  - Entered by the fork: table 1a0a6f380311 (hash checked), LABELS b2125a138866.
    - Checked against V4: L5199 is (c4-6-1), 𝔰(W) = n(W) + |𝓗(W)|/(LM), and L5249 is 𝔞_W = η𝔰(W).
    - Both entries read as proposed. TL #252's pin "V4 L5249" is to the use 𝔞_W = η𝔰(W), which is correct.
  - Fork, later: table 4e1fce093133 (hash checked), LABELS fc2e047f8356. #T12.25 now records BETA's Lemma D crossing reading of PRT2, marked inferred, not printed. No file of mine cites #T12.25 or #T10.53-0.
  - Fork, after BETA's R79o-f repairs: table bf83cc8bf06b (hash checked), LABELS feb4696088c9.
    - #T12.25 is split (#T12.25-0, #T12.25-0-1), as is #T12.25-2 (#T12.25-2-1).
    - #T2.6's source now names W-δ #W11.105-6.
    - No file of mine cites #T2.6 or #T12.25.
  - Fork, after a wording change to N(u) in #T12.25-0-1 (BETA #BV.3-2): table b80c8dc1f78a (hash checked), LABELS 899fee12c60f. Not cited by my files.
  - Fork, after BETA's R79o-g: table 72dfacb1fb72, then 30abf8470745. #T12.25-0 says PRT2 (2.46) does not fix whether a bond with end-points in two layers counts in one term or in both. Later rows are BV clash notes only. LABELS 5f5d7c7b57b0, LF 943491fdba44.

## EVAL: the crossed-layer increment of PRT2 (2.46) under both counts (20:33, 8 Nov)

- Found from the fork's #T12.25-0 note.
  - EVAL #44, #86.2-0 and #99 took "each fully crossed layer adds at least M (M₁ for a strip layer) to d" from (2.46). PRT2 p.231 l.7–12 prints Σ_j(L^jη)^{−1}|Γ ∩ B^j(Λ_j)| over contours of T_η, with |Γ| = η·(number of bonds).
  - The exact M depends on how a bond with end-points in two layers is counted, which PRT2 does not fix.
- Re-derived:
  - A bond of T_η with both end-points in B^m(Λ_m) counts in the term m under either count.
  - A contour's last site on one side of a crossed layer m and its first site on the other are at least ML^mη apart (the separation of #44-1), so the contour has at least ML^m − 2 such bonds between them.
  - So the layer adds at least M − 2L^{−m} ≥ M − 1 (m ≥ 1, L ≥ 2), and different layers use disjoint bonds.
  - For a strip layer the increment is at least M₁ − 1 ≥ M₁/2.
- Consumers rechecked:
  - #44-3: Le^{−δ₀(M−1)/16} ≤ 1 for M large given L.
  - #45: c′e^{−δ₀(M−1)/16}.
  - #86.2, #86.3: rate δ₀(M−1)/16.
  - #86.3-0: e^{−δ₀(M−1)/16} ≤ e^{−δ₀M/(16M₁)} ≤ e^{−1}L^{−(d+1)}, by M − 1 ≥ M/M₁ (M ≥ 2, M₁ ≥ 13) and #T4.32's condition, which is unchanged.
  - #99: unchanged condition δ₀M/(16M₁) ≥ (d + 1)log L + 1.
  - #99-1/#99-2: δ₀(M₁ − 1)/16 ≥ δ₀M₁/32 ≥ 2(12d + 1)log L ≥ (d + 1)log L + 1 for L ≥ 2.
  - #166's (n − k₀)M/M₁: unchanged.
  - BP_LFR2_REPLACEMENT #160.7 uses a sup-distance through LF #4.48-3.0.1, not the layer count: unchanged.
- Repair:
  - #44 is split into #44, #44-1 (the separation), #44-2 (the count) and #44-3 (the increment and the factor).
  - #99 is split into #99, #99-1 (the strip) and #99-2 (the constants). The pointer at #141 now reads #99-1.
  - The (2.46) restatement in #99 is deleted; it cites #44-3.
- Pins: PRT2 p.231 l.7–12 was read in p231_corrected.tex (l.7 |Γ| = nη, l.8–9 the admissible contours, l.10–12 (2.46)). The old "l.10–12" in #99 was deleted, and #42's "l.11" stands.
- Two rechecks done. Lines ≤ 600 except the pre-existing long #45 and #98. Labels give 1,114 tags. EVAL 45950657f90e, LABELS_TWO_LOOPS 598621d29d8e. The table needs no change.
- Follow-up:
  - #99's "M ≥ 2" is not a new lower bound. #44-3's Le^{−δ₀(M−1)/16} ≤ 1 with L ≥ 2 forces M − 1 > 0, so the integer M is at least 2; #99 now cites #44-3 for it.
  - EVAL a0e0c1913a11 (tags unchanged).
  - Fork: table c53644129e4c, LABELS e46877534696, LF 943491fdba44. New LF #0.0 rows (#T12.9-1-4 to #T12.9-1-6, #T12.12-1), and (D-Λ) and (D-P) added to #T1.5's lower bounds on M. None of my rows changed.
  - Fork: table fba275588b70 (hash checked), LABELS 36a9bad25b25, LF b78d00e57470. #T2.9 and #T2.15 now list LF #4.33's RM ≥ 4dL. EVAL #99-2 still reads correctly: #T2.5 has δ₀M′ ≥ 64 log L and #T2.15 has K ≥ 12d + 1.
  - Fork: table cf5cee0d186c (hash checked), LABELS 7803c1d272f3. #T2.9 now says where LF #4.33's ⅛δ₀RM ≥ 4 log L + 1 is met. No file of mine cites #T2.9.
  - Fork: table 3061088e4192 (hash checked), LABELS 194dab22d988, LF ba63d882f467. #T2.9 and #T2.15 changed. Rechecked that #T2.15 still has K ≥ 12d + 1 and #T2.5 still has δ₀M′ ≥ 64 log L, the two facts EVAL #99-2 uses.
  - Fork: table 2be3bbe61e07 (hash checked), LABELS 795417a12770, LF 88c95b028675. #T2.9 and #T2.15 changed. #T2.15 still has K ≥ 12d + 1 and #T2.5 still has δ₀M′ ≥ 64 log L.
  - Fork: table ffbd57502390 (hash checked), LABELS 22242682fb78, LF 1e6de3b6974e.
    - P_β and (D-P) are removed from #T12.9-1-4, #T12.9-1-6 and #T1.5.
    - #T1.5 still has M₁ = K_{M′}M′, which EVAL #99-2 uses.
    - No file of mine uses P_β or (D-P).
  - Fork: table ef144452169e (hash checked), LABELS fb109c5cfb6b, LF 16874c04b589. New row #T4.29-8 (n_F, n_F^c), and a clause deleted in #T4.29-4. No file of mine cites #T4.29 or uses n_F.
  - Fork: table 44e762855f6e (hash checked), LABELS 0486400accce. #T10.2 and #T10.3 are re-pointed from BFWL #B0.77 to #B9.89. No file of mine cites #T10.2, #T10.3 or #B0.77.
  - Fork: table 4195490cc3c6 (hash checked), LABELS 946d11d9064b. A BFWL pointer in #T10.2 changed, which my files do not cite.
  - Fork: table ee0bfb240690 (hash checked), LABELS 78d5306448d6, LF 272a46347af7. BETA's #T10.50, #T6.21 and #T10.28-4 changed. No file of mine cites them.
  - Fork: table 3c42a6bdb040 (hash checked), LABELS dfdc7501ce59, LF 1e51ad09b521. Only #T6.21's wording changed, and my files do not cite it.
  - Fork: table f989d53010a8 (hash checked), LABELS e28e13308100, LF 655cd900e6b3. BETA's #T10.28-4, #T10.1-1 and #T6.21 changed. No file of mine cites them.
  - Fork: table c42f30bb83d2 (hash checked), LABELS a387bd523e2f. LF packet-52 rows are new (#T12.9-1-7, #T12.9-1-8, #T4.29-9), and #T12.9-1 and #T12.12 were edited. Both "V4's hull size 𝔰(W)" clash notes are still in place.
  - Fork: table 9da2dd3270a0 (hash checked), LABELS 0a21409341bc, LF 410b1ad53094.
    - The new #T10.40-1 records that BFWL's C_α := C max(π^{1−2α}, π^{−2−2α}) (#B4.50) is not #T4.53's two-loops C_α.
    - Our C_α is the O(1) of (α′), D2.7's c_{α′} (TL #387). #T4.53 is unchanged, and so is the TL text.
  - Fork: table 8a5d58197039 (hash checked), LABELS f295fabf5ba8, LF 3e05922ac4b6, Cauchy 563cdd5a5b01.
    - Packet-52 boundary-term constants were added in the #T12.7, #T12.9 and #T12.12 families.
    - No file of mine cites #T12.7, #T12.9 or #T12.12, and both 𝔰(W) clash notes remain.
  - Fork: table f401812fa4b8 (hash checked), LABELS e96ca9a8a096. BETA's new row #T10.35-3 (BFWL Proposition 2.11's s) is not cited by my files.
  - Fork: table db0896812ee7 (hash checked), LABELS e9dadddbfe78. BETA's Proposition 2.14 rows #T10.37-1, #T10.37-1-1 and #T10.37-2 are not cited by my files.
  - Fork: table 613738bf5acc (hash checked), LABELS 5ae1d7f510aa, LF b3f44b51cb9c, Cauchy c9b62136d9c5.
    - #T12.14 now reads c_W := c_sh (map #MD2.0.3.48-2), also the LF's c_W in c^σ_n, not the Cauchy note's c_W of #C10.3.13-1 (#T12.7). The LF's former c_W (#5.33) is renamed c_{RW}.
    - TL uses c_W as map (12)(d)'s share constant (D2.6 closure 5.5; TL #346, #370, #484 and the e^{c_W} normalisations). That is the map's c_W of #T12.14, so nothing changes.
  - Fork: table dc6e150e2f12 (hash checked), LABELS 0a3b00f4d284, LF 9c2e58ac7bd3. A pointer for c′_W in #T12.9 changed. My files neither use c′_W nor cite #T12.9.
  - Fork: table a138f3b4afc3 (hash checked), LABELS 32065f9408ec. BETA's C_⊥ := π²/4 is in #T10.49-1, which my files do not use.
  - Fork: table 98ae321f3021 (hash checked), LABELS 6ac41862712f.
    - BETA's §7 rows changed: #T10.47-1, #T10.49-1, #T10.49-1-2 and #T10.49-1-3.
    - BFWL's Ψ is now marked as not #T12.20-4's Ψ(S) or #T12.15's Ψ°.
    - My files cite none of these rows.
  - Fork: table 0d89c0f3915d (hash checked), LABELS a12b80eab159, LF bd880a3e0982. #T10.49-1-3's wording and an LF pointer in #T12.7 changed. My files cite neither row.
  - Fork: table 511079111f74 (hash checked), LABELS 5bd68acf5d74. BETA's new row #T10.1-3 lists BFWL's several meanings of β and β′. It is BETA's own clash row, and my files do not cite it.
  - Fork: table a04e24238a0e (hash checked), LABELS 613e146f7d0a.
    - The β₀ clause of #T10.1-3 now names CRE (2.6)'s β₀, whose LF value #T1.2 fixes.
    - That is the β₀ my files use in (1 + β₀), so nothing changes.
  - Fork: table 30cf1840e816 (hash checked), LABELS 30867439b970. #T10.2 and #T10.3 are re-pointed to BFWL #B2.2.296–#B2.2.297. My files do not cite them.
  - Fork: LABELS e91509b34a29 at LF b6aff2179f62, a relabel only for LF packet 12b; the table is unchanged (30cf1840e816).
    - All 54 "LF #…" tags cited by my files still resolve in the LF.
  - Fork: table 8fe62fa8aa31 (hash checked), LABELS 06f719ef9966, LF e743322b1079.
    - New BETA rows #T10.28-0-1, #T10.28-3-0 (α₂), #T10.28-3-1-1 (δ_{RG2}) and #T10.28-4-2 to #T10.28-4-4, for BP_RG2_COMPLEX_B.
    - #T10.28-4-4 is RG II's ε₁ (g_k|B| < ε₁, p.6 l.57) and is marked as not VAR's ε₁.
    - My files use VAR's ε₁ (EVAL #45's r_B) and never RG II's, and they do not use α₂ or δ_{RG2}.
  - Fork: table 424462b70edb (hash checked), LABELS 282481040763, LF 4d0aca68af0c.
    - #T3.19's notes column now lists BFWL's uses of VAR's ε₁, and #T10.28-4-4 is now RG I's and RG II's ε₁. The definitions are unchanged.
    - My ε₁'s are VAR's (EVAL, BC), or carry a superscript (ε₁^{RG2}, ε₁^{JB}, ε₁^X, ε₁^*, ε₁^G). None is RG I's unmarked ε₁, so nothing changes.
  - Fork: table 1f09ad54e36a, then bafb79d6a633 (hash checked), LABELS d72e85e64e2a. New rows #T10.28-4-5 (RG I and RG II's a₁) and #T10.28-4-5-1 (BFWL's other a₁), then a cell fix.
    - My unmarked a₁'s are VAR's: EVAL #4 (VAR (172)), #93 (VAR p.305 l.6, read: "The condition M′ε₁ ≤ a₁ implies M′B₃ε₁ ≤ a₅"), #173.4, and BC #BC.3-1-1-2 and #BC.4-6.
    - BC also used a₁, a₂, a_i as lattice points (#BC.2-5-2–#BC.2-5-4 and #BC.3-1-3-0-1–#BC.3-1-3-0-3), in the file that introduces VAR's a₁ at #BC.3-1-1-2. Renamed to y₁, y₂, y_i; y_ was unused in BC.
    - The bond ⟨a, b⟩ with an unsubscripted a (#BC.2-3-3-1, #BC.3-1-3-1) has no subscript and is kept.
    - BC bde068e3d922, labels unchanged (1,114 tags).
  - Fork: table 2376a6eb9706 (hash checked).
    - BETA-side changes: #T10.28-4-2 drops w, and #T10.28-0-1 drops #BH.3-2.
    - LABELS stays d72e85e64e2a until (4) fixes a {#D.c_K₂} tag without ":=" in LF 6a8cf173c5ce.
    - My files cite none of these.
  - Fork: table 4e14a6057353 (hash checked), LABELS ba2e83b1fb71, LF 2c51f1f24191. #T12.9's c_ρ now has the new C_{K₂} and c_𝔯; my files use none of them.

## Structural review, resumed (user: "Go", 8 Nov)

- (a) One uniqueness lemma, BP_DERIVED_CONFIGS.md #BC.1-4-3.
  - Statement: 𝐁 under VAR's standing conditions, V with (7) at ε₁ ≤ a₁, and B₃ε₁ ≤ ε₀ ≤ a₀. A configuration critical for (5) on (6) has a critical orbit, by the invariance of (5) and (6) under (4) (VAR p.278 l.16–19, l.32–33). That orbit is the minimal orbit, the unique critical orbit (Theorem 1, p.279 l.8–15, read). So the configuration is F^w for every minimal F, U_𝐁(V) among them (#BC.1-4-2), with w = 1 at the points of 𝐁.
  - Consumers now citing it: EVAL #97.1 (with #94's ε₁ and ε₀ = B₃ε₁; stage n+1's minimiser lies in (8), so in stage n's 𝔘(B₃ε₁)), #103 (the w-in-(4) paragraph is deleted, as it is the lemma), #130.7, #173.4 (ε₀ = B₃ε₁ by #173.3.3; B₃ε₁^{JB} ≤ B₃ε₁ ≤ B₃a₁ ≤ a₀), and #191 (in place of "VAR Theorem 1 with map #MOMGD.11's uniqueness identification": U(𝐁, V)^v is critical at V^v, so it lies on the minimal orbit there).
  - BC #BC.4-6 and #BC.4-6-0 cite it. BC keeps its own open-subset step, which is specific to the (2) convention of #BC.4-3.
  - Two rechecks done. #BC.1-4-3 is 611 characters. EVAL 28cbe8d10275, BC ab5a9947754c, LABELS_TWO_LOOPS b53cb4603e1e (1,114 tags).
- Measured and sent to the fork as proposals 1–8, unranked here; see the message:
  - BETA's tags on fragments (3,000 of 3,642 tagged lines under 160 characters);
  - BETA §10's re-derivations from #B10.104 (~97k);
  - the map's gap block (127k: 7 OPEN lines, 118 status lines ~46k, #MOMGD.33 34.7k of derivation, 91 round mentions);
  - LF #0.1.2–#0.1.42;
  - W-δ §8 (36k, restating the table's stages), §10.6 (9.6k) and Open Gaps (22k);
  - the line-defect note's review history (97 round mentions, ~13k) and D2.6's (~7k);
  - #BC.1-4-3 for LF #3.85-1, #4.51-2-1, map #MOMGD.11 and #MD2.2.6.190-11;
  - the ε₁ monotonicity as one clause in #T3.19 (Cauchy #C9.1-1, W-δ #W8.12-8, #W10.5.96, §12).
- BETA §10 up to #B10.104 (27k) is new mathematics and was not proposed.
- Fork, first reply: items 1–2 went to BETA and 3–7 to (4); item 8 is in the table. Table d7fcd67ff35f (hash checked), LABELS 0f3c0a6da405, LF 3cd053fa2dff.
- Fork, correction: the clause is #T3.19-1. (7) is monotone in ε₁, but (9)–(10) hold only on cubes with M ≤ M(ε₁) = R₁M₁a₁/ε₁, so ε₁ ≤ R₁M₁a₁/M per cube. Table ac2097c365d6 (hash checked), LABELS 144d2b7725d9, LF d8dbfcb1b70a.
  - Re-derived: VAR p.279 l.9–28 and p.304 l.21, l.52–54 were read. Existence and uniqueness (l.8–15) carry no M(ε₁); the cube condition (l.17) does. p.305 l.6's M′ is VAR's own (R₁M₁)^{−1}M (p.304 l.21).
  - Repair, EVAL #94: "M′ε₁ ≤ a₁ (p.305 l.6)" had an undefined M′ that clashed with #99-2's table M′. It now reads M′ ≤ M(ε₁) = R₁M₁a₁/ε₁ at #T2.7's cube parameter M′, R₁M₁ being VAR's, which is p.305 l.6's condition with its M′ = M′/(R₁M₁).
  - Repair, EVAL #101: (9)–(10) on the cubes of parameter M′ ≤ M(ε₁) (#94), and (M′/(R₁M₁))B₃ε₁ ≤ a₅ (p.305 l.6).
  - Unchanged: #BC.1-4-3 and #173.3.3–#173.4 use only existence and uniqueness. #173.3.3 applies Theorem 1 at ε₁^{JB} ≤ ε₁, where M(ε₁^{JB}) ≥ M(ε₁).
  - Sent to the fork: #T1.5 and #T1.6 write M′ = R₁M₁, but #T2.5 and #T2.7 have M′ ≥ VAR's R₁M₁ and a multiple of it.
  - Recheck 1: both edits re-read; M′ in EVAL now appears only at #94, #101 and #99-2 (table M′). Recheck 2: p.304 l.21 and p.305 l.6 re-read; (M′/(R₁M₁))ε₁ ≤ a₁ is equivalent to M′ ≤ R₁M₁a₁/ε₁, and the implication to a₅ is VAR's.

- Fork, R₁M₁ resolved: table 9aa377dce076 (hash checked), LABELS 1b3dfa5d349d, LF a70ba5537db2. #T2.7 is the printed product. The new #T2.7-1 is the raised product R₁M₁ = M′ (R₁ raised to M′/M₁^{VAR}, BP_JOINS #4.23–#4.23-0), so M(ε₁) = M′a₁/ε₁, and #T1.6's a₁ and a₅ depend on M′.
  - Re-derived: VAR p.277 l.11–17 (R ≥ R₁, with R₁ and M₁ fixed so that [3, 5, 6] hold), p.303 l.36–41 ((162): B₃ depends on d and L only, not on R₁M₁), p.304 l.21–26 and l.52–54 (a₅ through (R₁M₁)² in (166), and a₁ through a₅), and p.305 l.30–36 (Sect. G: U₀ = U_k(V₀) with V₀ meeting (7), Sects. A–E repeated at the pair). PBG p.396: the cubes are unions of "several" big blocks of size O(1)M with O(1) ≥ 10, which is not VAR's class cube for cube.
  - EVAL #94 now has ε₁ ≤ a₁, with a₀ and a₁ taken at R₁M₁ = M′ (#T2.7-1, #T1.6) and B₃ independent of R₁M₁. The cube condition is dropped, since no cube of VAR's class is used.
  - EVAL #101 now reads: U₀ = U_k(V₀) is VAR's Sect. G base, and VAR repeats Sects. A–E at U₀ (p.305 l.35–36), applying PBG there. This replaces the (9)–(10) ↔ (3.35)–(3.36) identification, which matched no cubes.
  - BC #BC.3-1-1 is in the project convention: block size M₁^{VAR}, R₁ raised to M′/M₁^{VAR}, R := R′M′/M₁^{VAR} ≥ M′/M₁^{VAR}, and Ω^X_n a union of M′- hence M₁^{VAR}-cubes, since M′ is a multiple of the printed product (#T2.5, #T2.7). The separation R′M′ is unchanged, so #BC.3-1-2 and #BC.3-1-3-0 are unaffected.
  - BC #BC.3-1-1-2: a₅ and a₁ depend on R₁M₁ = M′ (#T1.6); B₃ does not.
  - GC #6.16.1-1-1 and #6.16.1-2: R₁M₁ is named as M′ (#T2.7-1); M^V ≤ CM/2 + (3/2)M′ ≤ M(ε^V_k) = M′a₁/ε^V_k for g small (ε^V_k → 0, #6.16.1-1), and s^U_n carries (1 + 3M′/(CM)).
  - Unchanged: MIXED #24 (BP-joins #4.22.1 already takes R₁M₁ = M′), and EVAL #46 (B₃ depends on d and L only).
  - Recheck 1: every changed line was re-read, and M(ε₁), R₁M₁ and (9)–(10) were grepped in all my files. Recheck 2: the cited VAR lines were re-read and the dependence claims compared with #T1.6 and #T2.7-1.

## Long lines (item 2 of "Go", 8 Nov)

- At 23:33 the lines over 600 characters were EVAL 84 (l.257 3,945, l.159 7,741, l.6 3,541), MIXED 14, NSTEP 5, GC 12, SECOND_CLASS 3, BC 1, LFR2 0. Lines up to about 650 characters are left as they are.
- Method: split at sentence boundaries into tagged sub-lines one indent deeper, with the wording unchanged (bookkeeping, no round).
- EVAL #197: split into #197-1–#197-8.
- Each split replaced the space after a full stop by a new line carrying the sub-line's tag; no word changed. New tags:
  - EVAL: #17-1, #66-1, #86.1-1-1, #91-1-1, #92-1, #93-1, #97-3-1, #116-2-1, #130.18-1, #173.7-1, besides the earlier ones.
  - MIXED: #5.3-1, #5.4-1, #5.4-2, #5.6-1, #5.8-0, #5.10-1–#5.10-3, #5.10.1-1, #5.10.1-2, #5.10.2-1–#5.10.2-3, #5.10.2.1-1–#5.10.2.1-3, #5.10.3-1, #5.10.3-2, #5.10.4-1–#5.10.4-7, #5.10.5-0, #5.10.5-1-1, #5.10.5-3-1, #5.10.5-3-2, #5.10.6-1–#5.10.6-6.
  - NSTEP: #3.2.1-1, #3.2.1.1-0-1, #3.2.1.2-1–#3.2.1.2-3, #3.2.1.2.1-1–#3.2.1.2.1-3, #3.2.2.1-1–#3.2.2.1-4.
  - GC: #6.2-1, #6.4-1, #6.4-2, #6.8-1, #6.8-2, #6.9-1, #6.9-2, #6.10-1, #6.11-1, #6.12.1-0, #6.14.1-0, #6.15-1, #6.16.1-1-1-1, #6.17-1, #6.17-2, #6.17.1-1, #6.17.1-2, #6.17.3-1–#6.17.3-3.
  - SECOND_CLASS: #805-1-1, #814-2-0, #819.1-1, #819.1-2.
  - TL note: #3-1, #3.2-1, #6-1, #6-2, #222-1, #222-2, #222.1-1, #224-1, #229-1, #230-1, #247-1, #249-1, #250-1, #332.1-1, #574-1, #617-0, #737-1, #737-2, #819-1, #820-1, #845-1, #868-1, #893-1.
  - N-loops: #NL1.1-1-1, #NL1.1-2-1, #NL9.6-2-1. The pair note has no line over 600.
- Left over 600: single sentences (EVAL #14-3 739, #197-5 672; MIXED #5.10.6-1 687), EVAL #88.1 (630; #88.1-0 and #88.1-1 are taken), BC l.51 (635), and lines of 601–629 characters.
- Checks: indentcheck.py on every file (no mismatch except the "-0-n" false positives #3.2.1.1-0-1, #6.14-0-1, #86-0-1, which sit two deeper than their "-0" parents); every new tag checked free across the note and its satellites; labels_two_loops.py: 1388 tags, no duplicate, no dangling reference.
- SHAs (9 Nov, 00:00): TL 69e4c14900cd, N-loops 718308bccdb0, pair 018a6b07701c, EVAL 315db9438efb, MIXED d6ea6cbbadeb, GC 6ed315284152, NSTEP 524b5f970a10, SECOND_CLASS 49569876a987, BC f84432e7cbdc, LABELS 3b7e835a3418.

## Fork messages (8 Nov, late)

- a₀: VAR ties a₀ to no R₁M₁ (p.280 l.42, p.294 l.47); a₅ depends on it through (166) (p.304 l.21–26), a₁ through a₅ (l.52–54), and B₃ does not ((162), p.303 l.41). #T1.6 says this. Table 025ddcb64cd8, LABELS 320d71db7f6c, LF 0c619919e05c. Consistent with EVAL #94, #BC.3-1-1-2 and GC #6.16.1-1-1, which claim the M′-dependence for a₁ and a₅ only.
- BETA rows #T10.1-3-1 (β′), #T10.1-4 and #T10.1-4-1 (γ), all BFWL meanings: table 4d40667f6419, LABELS d55e76411edb, LF 0c619919e05c. My files use β′ only in the pair note (#PC4.14-5.5.0.1, #PC4.14-6.4.1–#PC4.14-6.5), where it is #T3.6's; no effect.
- Table 16c2e6c39248 (hash checked), LABELS 3348e056288a, LF fb8554088cbd: R₁M₁ on the #T2.7-1 convention (BP_JOINS #4.23–#4.23-0), which EVAL, BC and GC follow; #T2.22 is now R_ι (lift) and defines no R₁, and no file of mine cites #T2.22 for R₁; #T4.42's y_c is written abs(e^{−d_c} − 1), with no content change, so #814 is unaffected.
- Table 7ee74ca1fafc, LABELS 3cf11fb749f4 (both hash checked), LF 5524a8de7a93: moved #B10 tags re-pointed to BETA's BP_FAMILY_* files; F(𝐔, 𝐉) is now #T12.24-1-0-1, T^loc keeps #T12.24-1-0; #T3.24's B_T′ source is LF #4.434.4-2. No file of mine cites #T12.24-1-0, #T3.24 or a #B10 tag; no effect.

## Structural review: the complex-gauge files (9 Nov, 00:31)

- Compared: GC, BC #BC.5–#BC.8, NSTEP #3.2.2–#3.2.2.1, LF's BP_COMPLEX_BASE_GAUGE.md (#4.536.1–#4.536.10, c1aa1eaecc5b) and BETA's BP_PBG_COMPLEX.md (#BX.1–#BX.11), with BP_PBG_DRESSED.md #BD.12.
- Repair, NSTEP #3.2.2.1-2: the recursion for w_m applies the covariance of the averages at the G^c-valued w_m, but the pin (CMP98 p.27 l.2–3) makes only the configuration G^c-valued. It now cites p.27 l.30 as well, where CMP98 applies the covariance at the v of (62) (p.28 l.29), an exponential of logarithms of the complex V₁, so G^c-valued.
  - Recheck 1: p.27 l.2–3, l.30 and p.28 l.29 re-read in the corrected transcript; the identity at l.30 is \bar V_c = v(c₋)(\overline{V_1V_0})_cv^{−1}(c₊) with V′ = V₁^v G^c-valued (l.3). Recheck 2: the use at w_m needs exactly that identity at U_k(d_m) and w_m; #3.2.2.1-3's bound on w_m is unchanged, and no other line of mine cites p.27 l.2–3.
- NSTEP #3.2.2.1-2's axial statement is also LF's #4.536.2-2; both derive it from REG (1.19)–(1.20) in one sentence, so NSTEP keeps its own.
- BC #BC.5-1-3-1-0–#BC.5-1-3-1-1 and #BD.12-3 both take CMP98's axial gauge on a box, under different hypotheses (VAR's plaquette bound L²B₃ε₁L^{−2n} against PBG's class cubes and 12Mα₀); both stay.
- GC #6.16.3-2 cites BC #BC.5–#BC.7, and GC #6.10, EVAL #114 apply the totally-real identity theorem to different manifolds (G in G^c, 𝓜 in 𝓜^c), one clause each.
- Sent to the fork: LF #4.536.2-1 derives the covariance of the averages at G^c-valued g from log(gXg^{−1}) = Ad(g)log X for X near 1. CMP98 prints this as (57), R(X)f(Y) = f(R(X)Y) for every invertible X and analytic f (p.27 l.9, l.17), and applies the covariance at a G^c-valued v at p.27 l.30 ((62), p.28 l.29). So #4.536.2-1 can cite these instead, and its restriction to |log g| small is not needed.
- SHAs: NSTEP 44f3dcb5e76b, LABELS_TWO_LOOPS 3b7e835a3418 (1388 tags, unchanged).
- Fork: table cc1e4b4dc203, LABELS 7cfd923fd769 (both hash checked), LF d0574944e800. (4)'s D-tag renames in #T4.27, #T4.29-6, #T12.9, #T12.9-1, #T12.12 and #T10.58; BETA's BH constants in #T10.28-3-1, #T10.28-3-1-2, #T10.28-3-1-3 and #T10.28-4's note; #D.c_R is now c_rad (#4.290-2), #D.α′ is now α^ι, and #D.ε₁.3 is now ε₁^D. None of my files cites any of these rows or tags; no effect.
- Fork: table b98cd2b67e3b, LABELS 87eb0ce176a3 (both hash checked), LF 2c3464886d64. Only #T10.28-3-1-2 (BH notation) changed; none of my files cites it.
- Fork: table e97456cf4748, LABELS 8b437a510332 (both hash checked), LF ef0e13498e09. Only #T10.1's scope wording changed; none of my files cites #T10.1.
- Fork: table aa47849f0414, LABELS 74d1df0f4085, LF 6b0fec6686fa (all hash checked). (4) deleted LF #0.2–#0.19 (#0.1.x unchanged) and the table rows were repointed. No file of mine cites #0.2–#0.19 in any form (LF #, "its #", "the large-field note's #"); no effect.
- Fork: table 324370d32db5, LABELS d891790f6eed (both hash checked), LF 6b0fec6686fa, Cauchy 21f829a454ae. Cauchy #CP.6-x, #CP.10, #CP.11-3 and #CP.21-x deleted; none of my files cites them. #T11.17's uniqueness clause now cites EVAL #130.8–#130.8-4; re-read: #130.8-4 gives the representative e^{iη(a″+𝓗^h)}U_{k+1} that the clause states, through Theorem 4's uniqueness (#130.8-2–#130.8-3) and (190). Told the fork the tags stay and that I will announce any move.
- Fork: table 254de9ef4c23, LABELS e21e34801154 (hash checked). #T3.34's β ≤ 1/5 cites EVAL #73–#75-2, and #T3.39 cites #14, #75-2 and #86.3. Re-read: #75-2 derives β ≤ 1/5 from the budget of #73–#75-1 (correct). #14 has no β condition; β ≤ 1/4 is used at #14-2, #86.3, #130.15.2-5, #137-1, #166-3, #166-4, #199, #210 and GC #6.14-0-1. Sent the fork the correction #14 → #14-2 and the full list; the tags stay.
- Fork: table ea5ea99a8e8f, LABELS 67b19e855937 (hash checked). #T3.39 now reads "β ≤ 1/4 (#14-2, #86.3, among its uses)" and cites BP_TL_EVAL_POINTS #14-2, #75-2, #86.3; re-read, correct.
- Fork: table f9c64b74645d, LABELS 20684a60a450 (hash checked), LF 5e7dd17a4e72. BETA's BP_RG2_COMPLEX_B rows #T10.28-3, #T10.28-3-0, #T10.28-3-1-2 (with -2-1, -3, -3-1) and #T10.28-4-2-1 changed; none of my files cites a #T10.28-3 or #T10.28-4 row.

## Structural review: the notes against the map, D2.6 and D2.7 (9 Nov, 01:56)

Repairs (each re-derived, every cited line re-read, two full rechecks of every changed line):
- GC #6.15-1 (error): C_av = 2B₃ replaced by (K3)'s C_av = 2(B₃ + 2c_dB₅), table #T4.45, as map #MDD2.4.4.16 has it; the pin "(l.168)" removed. c₀ is chosen after C_av, which is a constant of d and L (B₃, B₅ by VAR p.279 l.28, p.305 (173)), so c₀ stays a constant of d and L and #58 is unchanged. No other line of mine used 2B₃.
- GC #6.13-0: the restated x_n := β2^{−(k+1−n)} replaced by table #T4.49; the coefficients stay, as #6.13-1's arithmetic uses them.
- GC #6.8-1: the B-term argument restated from EVAL #153-1 replaced by a citation of #153-1.
- EVAL #61-2: the copy of the map's recursion and of C_S′ replaced by map #MD2.4.12.49-3–#MD2.4.12.49-4, #MD2.4.12.51 and covariance note §4, keeping the three inputs #62–#64 use (N^{(j)}, the carry term, Ĉ). #66 uses C_S′'s two entries, which the map row defines.
- Live-note line pins replaced by item citations: EVAL #56 and GC #6.15 (SW l.93 → SW closure §6(6b)); EVAL #62 (covariance l.131 → §4); EVAL #70 (SW l.95 → §6(6c); covariance l.20, l.26–29 → §0; l.87 → §3; l.13 → (K3); l.110 → §3(b)); EVAL #14-3 (D2.6 l.70–73, l.73 → D2.6 §3 *Size at U_{k+1}*); EVAL #67, #67-1 (D2.6 l.89 → 5.2), #68 (l.96 dropped, §5.4 named); EVAL #188 (D2.7 l.6, a summary of TL #7 → TL #868); TL #613 (D2.7 l.175; D26 l.136 → D2.7 15.5; D2.6 7.1), #728.1 (pin dropped, 15.5(ii) named), #728.2 (→ 15.5(ii)), #820 (D2.6 l.143 → D2.6 7.2's small-domain branch), #847 (closure l.136–138 → D2.6 7.1–7.2). Each target line read and its item identified.
- EVAL #14-3 (739 characters) split at a sentence boundary into #14-3 and #14-3-1.
- N-loops #NL6B.2-3, #NL6B.2-4, #NL6B.3 (error): they carried a superseded version of TL #660–#662 and #666 (Σ_PD_P, C^R, e^{−c_FDL^m/(2M)}, 12M/(c_FD)). Re-derived from the current TL: #660's chain gives Σ_P(D_P + 2ℓ_P) ≥ DL^m/M for any two loops; three gas sums per loop with #661 give 3·2^{d+2}C_KPℓ_ΣL^m ≤ C^×_{KP}ℓ_ΣL^m, so #662 and #665–#666 hold with ℓ_Σ. #NL6B.3 now cites #663 instead of restating its display. #NL10.5 (error, same source): C^R replaced by "#PC5.2-5 with ℓ_Σ in place of ℓ₁ + ℓ₂"; #NL5.4–#NL5.5 checked against #450, #452, #881.
- N-loops #NL1.1-1, #NL1.1-1-1: the restatement of TL #332.1 replaced by a citation; #NL1.1-1-1 merged (cited nowhere).
- Pair #PC5.4 (serious): the young cross part cited #C7.6-6-1–#C7.6-6-8, which hold the carried wraps at run A's (#C7.6-6-4-5), but had neither the step that moves them to run B's (the Cauchy note's #C7.8-9-9) nor the wraps' part of the marked activities' differences in its disc (ρ^E_K's second term, #C7.6-6-4-4). Repaired in place: #PC5.4-1.2 and #PC5.4-2.1 take the disc 1/(2ρ^{E,×}_K + 2x̄_K), x̄_K of #PC4.14-1.6.1 bounding that part (#PC4.14-6.7); new #PC5.4-2.2–#PC5.4-2.2-3 move the T-part activities along #PC4.14-1b.1's c^t and the slot-held wraps linearly on abs(t) ≤ R^×_t := min(u₀, μ^×_w/Δ̄^w_K), with Δ̄^w_K := 2τ^{w,×}_K + D^{cw}_K (#PC4.14-1b.4.4, #PC4.14-5.5.1) and μ^×_w from #893 and the sum lemma; there ε̂ ≤ ν_r/(2592M) (#PC4.14-1b.2) and the wraps are at most twice their bound, so Cauchy's estimate adds y^×_K := c″D^{cw}_K + 2Δ̄^w_K/μ^×_w. #PC5.4-3's Δ^{E,cr}_K gains 4x̄_K + y^×_K, summable by #PC4.14-5.6 and #PC4.12.1. #PC4.4-1's threshold now has ρ^{LF,×}_K + x̄_K ≤ ¼, which also gives the discs of #PC4.14-1.6.1 and #PC4.14-6.7.1 radius ≥ 2 (previously unstated), and 2Δ̄^w_K ≤ μ^×_w. No circle: D^{cw}_K and x̄_K are formulas fixed before K₁^×. N-loops inherit both through #NL10.4 (K₁^× with §6–§7's constants, τ^w and D^{cw} with ℓ_Σ) and #NL7.1-4 (#893's C_w per lineage).
- New symbols for the table (to the fork): μ^×_w, Δ̄^w_K, R^×_t, y^×_K (#PC5.4-2.2, #PC5.4-2.2-3). Grepped: no clash in the table, the notes or balaban_proofs.
- To the fork for (4), D2.7 15.8(c): its small-domain argument re-derives SECOND_CLASS #819.1–#819.1-2 and TL #820 at length, and its cost inequality "3 + p₀(g_k)/16 + 7.3's costs at Y_i ≤ ¼p₀(g_k)" omits TL #820-1's factor e^{A_k} ≤ e of the leading word's transports in Y_i's 100MR_k-cube (+1 in the exponent; the margin absorbs it for small g_k).
- Checked, no change: pair #PC5.4-1–#PC5.4-1.1 already cite #C7.6-6 and add only the pair's changes; NL #NL5.4 is #450 with ℓ_Σ.

Checks: labels_two_loops.py 1389 tags (one new, #14-3-1); labels_pair_cauchy.py 321 tags; no duplicate #NL or #PC tags. Table 9001e06afe10, LABELS ed8bc70a7fda (hash checked; #T4.45, #T4.49 re-read). SHAs: TL c94fec2689cb, pair ba015a19bf8d, N-loops 28632adfa662, EVAL 1a0a4186ca0c, GC e164be489ce0, LABELS_TWO_LOOPS cbe9269d767d, LABELS_PAIR_CAUCHY 12cd6886e722. No EVAL tag that the table cites (#130.8–#130.8-4, #14-2, #73–#75-2, #86.3) changed.
- Fork: table 203f57c6c6fd, LABELS ddebfda5b19c (W-δ batch, #T12.6's ℒ_ι, new #T12.9-1-8-2), then 9001e06afe10, LABELS ed8bc70a7fda (#T3.20 only). None of my rows; none of my files cites #T3.20, #T12.6's ℒ_ι or #T12.9-1-8-2 (grepped).
- Fork: table f0d3b556e982, LABELS 96f4c251b14e (hash checked), LF e6e9651b0809. New row #T12.3-5-1 holds μ^×_w, Δ̄^w_K, R^×_t (u₀ cited to #T4.55) and y^×_K; re-read against #PC5.4-2.2 and #PC5.4-2.2-3, identical. The fork re-derived μ^×_w's bound and y^×_K's inequality, found no row restating K₁^× or Δ^{E,cr}_K, and relayed the two D2.7 15.8(c) points to (4).
- (4): D2.7 15.8(c) repaired (ab2af6b0f234). It adds TL #820-1's +1 and cites SECOND_CLASS #819.1–#819.1-2; checked by grep against both.
- Table 52ddcf3354b9 (02:01) and LF a72fcc212da1 → b33bf407cd47 → 2dc2e4ffb4ef (02:09 on) changed with no message yet. LABELS 96f4c251b14e is unchanged; #T12.3-5-1 is re-read and still identical to #PC5.4-2.2–#PC5.4-2.2-3.

## Pre-check: pc-wraps-20261109-r1 (9 Nov, about 02:15; launched as task b38fwpavj)

Narrow round: pair #PC4.4-1–#PC4.4-1.1 and #PC5.4–#PC5.4-3, N-loops #NL6B.2–#NL6B.3 and #NL10.5. Spec spec_pc_wraps_r1.json.
- Every changed line re-read twice. The Cauchy steps are re-derived: for f analytic on abs(z) ≤ R, R ≥ 2, abs(f(1) − f(0)) ≤ sup abs(f)/(R − 1) ≤ 2 sup abs(f)/R. This gives 4(ρ^{E,×}_K + x̄_K) for the ς-step and 2/R^×_t ≤ c″D^{cw}_K + 2Δ̄^w_K/μ^×_w for the t-step, with 2/u₀ = c″δε̂_i.
- μ^×_w re-derived: n = i − j, L^{K′−j} ≥ L^n, and #C7.6-7-1 (m ≥ 1) plus the term n = 0 give e^{−a}(2 + 6/a) at a = c_wN_s/M. Δ^w_i ≤ 2τ^{w,×}_K + d^w_i, with d^w_i ≤ e^{cw}_i ≤ H^{cw}_i ≤ D^{cw}_K (#PC4.14-5.4.1, #PC4.14-5.5.1). On the t-disc the wraps are ≤ μ^×_w + R^×_tΔ̄^w_K ≤ 2μ^×_w.
- NL #NL6B.2-2's inclusion–exclusion is re-derived cluster by cluster: |S| = 0 gives v_∅ − v_∅ = 0, and |S| = 1 gives 0.
- Repairs in this pass:
  - #PC4.4-1: the condition "ρ^{LF,×}_K + x̄_K ≤ ¼, so ρ^{E,×}_K ≤ ¼" did not state what #PC5.4-2.1 uses. It now reads ρ^{E,×}_K + x̄_K ≤ ¼ (#PC4.8-6, #PC5.4-2.1). #PC4.14-1.5 and #PC4.14-6.7.1 need no threshold, since LF #5.38.2's 8ρ bound holds for every ρ.
  - #PC4.4-1.1: x̄_K and Δ̄^w_K → 0 added (#PC4.14-5.6, #PC4.12.1); μ^×_w does not depend on K.
  - #PC5.4-2.2-2: "without old components" added.
  - #PC5.4-2.2-3: u₀ ≥ 2 now cites δε̂_i ≤ D^{cw}_K ≤ ν_r/(10368M) (#PC4.14-1b.6, #PC4.14-3), in place of #PC4.14-4.4, which is at the step i − 1.
  - Definition check: "C := C₁ ⊔ C₂" → "C₁ ⊔ C₂ for C" (#PC5.4-1); "c^t :=" → "#PC4.14-1b.1's c^t =" (#PC5.4-2.2); "n :=" → "summed over n = i − j" (#PC5.4-2.2-1); "S := S(c)" → "With S = S(c)" (#NL6B.2-2). allow_defs covers the N-loop E^{R×}_k (table #T4.52's at N_C = 2).
- K₁^× is in no table row (grepped). Users of #PC4.4-1: #PC2.4-6, #PC4.8-6, #PC5.4-2.1, #PC8.1.1 and #NL10.4, all consistent.
- Lines ≤ 600 characters; 321 pair tags; no duplicate #NL tags. Reviewed blocks: 6.6k characters (packet 26.7k with context).
- SHAs: pair 295cf052fefd, LABELS_PAIR_CAUCHY rebuilt, N-loops baa8bb1afe79, TL c94fec2689cb, LF 2dc2e4ffb4ef. No known weak point.

## Fork: the ε₁ merge (9 Nov, 02:20)

- Table 26a3b26e4bd7, LABELS add96c31c8ee and LF 43055b036933, hash checked. LF #D.ε₁.2 is deleted, and ε₁ is LF #1.6-1's. No line of TL, the pair note, the N-loops note or my balaban_proofs files cites #D.ε₁.2 or LF §1's ε₁ (grepped). EVAL #44's ε₁ is VAR's own. Acknowledged to the fork.

## Heading-name citations re-pointed to tags (9 Nov, 02:23)

Bookkeeping, no bound changes, made while pc-wraps r1 runs (its snapshot is frozen). A scan of my files listed every italic heading name that matches no heading in the same file.
- Cross-file names, now cited by tag:
  - TL #6, #7, #222–#231, #374, #492, #493, #619, #864, #872: EVAL #13, #47, #48, #54, #55, #56, #72, #80, #110, #129, #130.1, #130.6–#130.7, #137, #138, #173 and #169–#172-2. The stale "(iii)," prefixes went with them; in EVAL itself "(iii)" is its part #90 and stays.
  - EVAL #59 ("map (6)(e)"), #60 (#223), #84 (#819), #87 (#868), #96 (#862), #188 (one #868 kept).
  - GC #6.2 (#110, #116, #105), #6.4-1 (#138), #6.7 (#123), #6.8 (#130.6–#130.7), #6.11 (#129). MIXED #5.1 (#45), #5.10 (#102). Pair #PC4.14.4-4.5.4-8 (#815).
  - TL #257: "(map #MD2.4.12.19)" in place of the bare *Arc cubes*.
  - TL #783: the line pins l.59, l.63, l.65 into D2.7 are removed; D2.7's *Corrections* (a), (b) are named.
- #872: "(#168). A_k is defined as a bound in #77" pointed at the wrong lines. A_k is defined at #169, and the phase-only use is #172-2. The line now reads "through A_k (#169–#172-2)".
- *Cubes* matched no heading in any file; it was already dangling in r37's snapshot. The count it stood for is now #628-1-3–#628-1-3-1. For closed cubes of side s, a tree of length ℓ meets at most 2^{d+1}(ℓ/s + 1) of them, and they are ∗-connected. The proof cuts a closed walk of length 2ℓ into ≤ 2ℓ/s + 2 arcs of length < s. Each arc meets ≤ 2 closed intervals per coordinate, which holds because the length is < s. RG I's d_k tree lives in the continuum (p.257 l.14–19), so the closed-cube version is the one #637 needs; the block version follows from it.
  - #613-5 and #637 cite #628-1-3 with s = MR_k; #699-3's use is the chain bound (#627, #635).
  - This is new content in (6B)-a, so it goes into that part's round.
- Lines above 620 characters, not touched here: EVAL l.123, 130, 201, 283, 435; GC l.49; MIXED l.56. They are split when those files' parts are next built.
- SHAs: TL ff04cff5e870 (1,391 tags), pair 391fbb4380ba, EVAL 7d859b9a5910, GC c1990909723c, MIXED ad2f29c7e27e, LABELS_TWO_LOOPS 4278370c6677, LABELS_PAIR_CAUCHY ceffe9b5bf0e.
- Later TL citations, same kind: #714-1 and #637-1 cite #628-1-3 with s = M; #665 cites "the first bound of the sum lemma #876"; #737-1 cites "D2.6 closure 2.1, *Merged groups*". TL 61c18f089b71, LABELS_TWO_LOOPS 4278370c6677 (1,391 tags).

## Triage: pc-wraps-20261109-r1 (9 Nov, 02:40)

Verdict: no fatal finding, one serious (S1), five minor (S2, M1–M4). Not clean, so the count stays 0. Everything else is CORRECT: (a), (b), (e), (f), the order of the steps, and the N-loops identity and pinning.

| Finding | Where | Repair |
|---|---|---|
| S1 serious: ε̂ ≤ ν_r/(2592M) does not double (T′)'s amplitude for the moved T-part activities | #PC5.4-2.2-2 | #PC5.4-2.2–#PC5.4-2.2-4 rewritten (below) |
| S2: μ^×_w carries e^{−c_wN_s/M}, so K₁^× and y^×_K depend on the volume | #PC4.4-1, #PC5.4-2.2-3, #PC5.4-3 | removed: the 𝐑-part holds no carried insertion (#658), so μ^×_w, Δ̄^w_K, R^×_t and y^×_K are gone |
| M1: Δ^w_i bounding the reference-activity differences was implicit | #PC5.4-2.2-1 | moot: the slot-held wraps step is deleted |
| M2: ρ^{E,×}_K → 0 needs ρ^{E,×}_K ≤ ρ^{LF,×}_K | #PC4.4-1.1, #PC5.4-3 | stated, citing #PC4.8-7.1 |
| M3: (2 + 6/a) where #876 gives (1 + 6/a) | #PC5.4-3 | S^cr ≤ e^{−a^cr_E}(1 + 6/a^cr_E) (#876) |
| M4: i > k − m_K and i > K′ − m_K side by side | #PC4.4-1, #PC4.4-2, #PC4.8 | #PC1.1-1 now reads k := K − j = K′; #PC4.4-2 uses k; the restatement in #PC4.8 is deleted |

Repair of S1, re-derived:
- Structural fact. TL #658 says no carried insertion enters 15.4's flat-reference gases; D2.7 15.8-1(2-2-1) says "its groups' slots hold no insertion (15.4(i))". So E^{R×} does not depend on the wraps. The marked activities' part from the occurrences' wraps is already in the ς-step (#PC5.4-1.2, x̄_K). Only the T-part activities remain at c^0.
- The disc is |t| ≤ u₀, with c^t = c^0 + tδc.
- Weights. e^{2a°} = e^{(ν/16)σ_i} is at most e^{s+(ν_r/16)σ_i}, because ν_r = ν and s ≥ 0:
  - sh, b and c_sh are nonnegative (map #MD2.4.12.21-1, #MD2.4.12.27-3, #MD2.4.12.23-2);
  - C_pc = 483C_τmax(C_τ, C_ℓ) with C_τ ≥ 1, and C_pc′ = C_pce^{40c_πα} ≥ C_pc.
- Positions. A group incompatible with 𝒢 lies at one of 𝒢's positions, and positions ≤ 81Mσ (map #MD2.4.12.38-1–2). A group whose arc holds b lies at b (map #MD2.4.12.28's "v at p").
- FV's condition at a = a°. Map #MD2.4.13.4 states it as Σ_{𝒢′≁𝒢}|c|e^{2a°} ≤ a°(𝒢). A priori the left side is ≤ a°/2 (map #MD2.4.12.51-4: C_S′ρ·pl ≤ ν/(64·81M); (S-w)'s weight e^{θ+ν_rσ+ν_e·ext}ℓ_X dominates e^{2a°}). This holds at the enlarged amplitudes (#590, #PC5.4-2). The moved part adds at most 81Mσ·u₀δε̂_i = 81Mσν/(5184M) = (ν/64)σ = a°/2. The total is a°.
- Linearity. (T′)'s chain Σ_{Γ∋b}|Φ°|e^{a°} ≤ Σ_{𝒢∋b}|c|e^{2a°} (map #MD2.3.5.3-1) makes #449–#450 linear in r°. #450 with r° in place of C_S′𝔞 and ℓ_i, D ≥ 1 gives 16e^{c_dr₀}r°(ℓ₁+ℓ₂)L^{m′}e^{−c_dL^{m′}}, with m′ ∈ {m, m + 1}. This is ≤ A^T_Er°L^me^{−c_dL^m}.
- c_d = ν/(32A_dML) has no amplitude in it, so a^{cr,2}_E ≤ c_d.
- Cauchy on R = u₀ ≥ 2 gives (2/u₀)(A^{cr,2}_E + A^T_Eu₀δε̂_i) = δε̂_i(c″A^{cr,2}_E + 2A^T_E) ≤ D^{cw}_K(c″A^{cr,2}_E + 2A^T_E).
- Assembly. Summing the ages m ≥ 0 gives the ς-step 4(ρ + x̄)A^{cr,2}S^{cr,2}, the t-step D^{cw}(c″A^{cr,2} + 2A^T)S^{cr,2}, and the 𝔷-removals 2·2e^{−C_Pk/4}A^crS^cr.
- Consumers:
  - #PC5.5 uses Δ^{E,cr}_K only as a summable number, and it is: ρ^{LF,×}_K, x̄_K ∝ D^{cw}_K, and D^{cw}_K, with A^T_E constant.
  - NL #NL10.5 now states the transfer: #NL6B.2's gases are 15.4's flat-reference series, the groups are #NL5.1's, #NL5.4 replaces #449–#450, and ℓ_Σ goes into A^T_E.
  - K₁^× (#PC4.4-1) no longer carries the μ^×_w condition. K₁^× ≥ K_Q gives u₀ ≥ 2.

Pre-check of the repair:
- Every changed line re-read twice.
- Removed symbols grepped in all notes, balaban_proofs and the table. μ^×_w, Δ̄^w_K, R^×_t and y^×_K survive only in history files.
- New symbols r° and A^T_E: no clash. ϱ was avoided because it is #T3.17's.
- Line #PC5.4-2.2-2 was split at 789 characters into #PC5.4-2.2-2.1.
- Size of #PC5.4-2.2–#PC5.4-3: 2.6k characters before, 3.4k after. The growth is new mathematics: the weight comparison and FV's condition.

Messages:
- To the fork: replace #T12.3-5-1 with r°(c) and A^T_E. Done. The fork re-derived a°/2 + a°/2 = a° and the Cauchy step, and cites r° at #PC5.4-2.2-2.1. Table 13584c7ab9d3, LABELS 2afdee6592fc, LF 8b6390bc65b9.
- To the LF session: #C7.8-9-9–#C7.8-9-9-1 has the same structure as the old pair step.
  - The 𝐑-part sees no wraps (D2.7 15.8-1(2-2-1)).
  - "every constituent at most twice its bound" needs the root-sum argument for the T-part, whose c^t is polynomial in t there.

SHAs: pair 59a17bcaf243 (324 tags), LABELS_PAIR_CAUCHY 4f9dce4f348e, N-loops 6d6f743c956c.

## Pre-check: pc-wraps-20261109-r2 (9 Nov, 02:42)

- A narrow round. Under review: #PC4.4-1–#PC4.4-2, #PC5.4–#PC5.4-3 and #NL10.5. Context: the new inputs (TL #435–#450, #589–#591, #656–#666, #876; NL #NL5.1–#NL5.6, #NL6B.2–#NL6B.3; the pair's #PC4.8-5–#PC4.8-8.2, #PC4.14-1–#PC4.14-1b.6 and #PC1.1–#PC1.1-1).
- Reviewed blocks: about 5.9k characters of the pair note plus 0.9k of NL. The argument field is 28.0k with context.
- After the triage the definition check found c^t defined twice. #PC5.4-2.2 now cites #PC4.14-1b.1's c^t, with t now in ℂ. Check: 0 conflicts.
- Every changed line re-read twice, and the re-derivations are in the triage above. The changed lines are #PC1.1-1, #PC4.4-1, #PC4.4-1.1, #PC4.4-2, #PC5.4-2.2, #PC5.4-2.2-1, #PC5.4-2.2-1.1, #PC5.4-2.2-2, #PC5.4-2.2-2.1, #PC5.4-2.2-3, #PC5.4-2.2-4, #PC5.4-3 and #NL10.5. TL #665 changed only its citation, to "the first bound of the sum lemma #876"; it is context here.
- Cited displays quoted and checked:
  - #658 "No carried insertion enters them";
  - D2.7 15.8-1(2-2-1) "its groups' slots hold no insertion (15.4(i))";
  - map #MD2.4.12.51-4 "positions of 𝒢 ≤ 81Mσ_{k+1}(𝒢), times C_S′ρ_{k+1}pl ≤ ν/(64·81M)";
  - map #MD2.4.13.4 "Σ_{𝒢′≁𝒢}|c_𝒢′|e^{2a°(𝒢′)} ≤ a°(𝒢)";
  - map #MD2.3.5.3-1's chain;
  - map #MD2.4.12.38-1–2's positions and (5.10) reduction;
  - map #MD2.4.12.26-1's C_pc;
  - #PC4.8-5.2 "ν_r = ν = η";
  - #876's Σ_{m≥0} ≤ e^{−a}(1 + 6/a).
- Directions checked: e^{2a°} ≤ e^{s+(ν_r/16)σ} needs only s ≥ 0. u₀δε̂_i = ν_r/(5184M) exactly. 2/u₀ = c″δε̂_i.
- Table: #T12.3-5-1 holds r°(c) and A^T_E (13584c7ab9d3); the reviewed lines define them in the note, and the row cites them. No restatement of a row in the lines.
- No known weak point is in the packet. Queued repairs for later packets are the TL (6B)-a items, all already applied.
- SHAs: pair 181c597efb6f, TL 61c18f089b71, NL 6d6f743c956c, LF 8b6390bc65b9, table 13584c7ab9d3.

## Bookkeeping: TL (6B)-a definitions for tl-6ba-20261109-r1 (9 Nov, 02:51)
The definition check on spec_tl_6ba_r1 found 8 conflicts. They are resolved as follows. None of these changes alters a bound, and all are made outside pc-wraps r2's lines under review (TL is context in its snapshot).
- #609: "with C := C₁ ⊔ C₂" now reads "with C = C₁ ⊔ C₂ (#332)", the line that defines C. The unused "and put m := K′ − k" is deleted; #707 and #885 state their own m.
- #613: C_a is renamed C_{α,k}. It clashed with #T4.39, and its only use is #613.
- #613-5 and #613-6: the cube count m is renamed |S|, with n in the count of the ∗-connected sets.
- #613-7: x is renamed ξ_η, and the sum is now Σ_{n≥1}ξ_η^n.
- #613-2-1 now reads "C_α and t_k of #T4.53", and #613-4 "with c_r and c_r⁺ of #T4.53". Both restated the row before.
  - #613-7 now reads "#T4.53's t_k gives δMt_k ≤ δM + 2log α_{1,k}^{−1} + log(L⁴R_k²)". Re-derived: t_k ≤ (32/(δ₀M))(2log α^{−1} + log(L⁴R_k²)) + 1 and 32δ/δ₀ ≤ 1 (#728.1).
  - c_r's value is #613-6's count, 3^d(3^d + 2^dM)·18.05σ(D).
  - c_r⁺ = C_αe^{δM}c_r is #613-7's last step.
- #625 now reads "So these groups take c_g = 0 (#T4.51)".
- #728.1-1 now reads "fixes t_k (#T4.53)".
- Clash grep: C_{α,k} and ξ_η occur only in TL.
- spec_tl_6ba_r1: claim (d) and Q3 now say c_g = 0 (#T4.51). Check: 0 conflicts.
- The fork was asked to re-point #T4.53's source column (t_k to D2.7 15.5 and #613-7, c_r to #613-6, c_r⁺ to #613-7); no values change.
- Rechecked twice: #613-5–#613-7's count and arithmetic were re-derived (the 𝒦 ↦ cube-set injection, (e3^d)^n, |S| ≤ 2^{d+2}ℓ/(MR_k), Σξ_η^n ≤ 1, and 1/8 − 1/512 = 63/512). The consumers of #613-2-1, #613-4 and #625 were grepped (#728.1-1 re-pointed; #565, #742-1 and #286's conditions are unchanged).
- SHAs: TL 2b71eba97d4a, LABELS_TWO_LOOPS 991d3da45044, table 5f928e9217c8 (fork, BETA rows only). The fork re-pointed #T4.53's source column (table 7738cc6e6c77), values unchanged.

## Triage: pc-wraps-20261109-r2 (9 Nov, 02:57)
Verdict: no fatal or serious findings and 7 minor ones, so the round is not clean (count 0). The referee checked the rewritten t-step and found it correct: (T′) is linear in r°, and u₀ uses exactly the a°/2 margin.

| # | Finding | Repair |
|---|---|---|
| 1 | #PC5.4-2.2-2.1 calls the condition "FV (5.11)'s"; map #MD2.4.13.4 labels it FV (5.10) for the tilted activities, and (5.11) is the conclusion | Reworded: "is FV (5.10) for the tilted activities abs(c^t)e^{a°} at a = a° (map #MD2.4.13.4), so by FV (5.11) the series converge" |
| 2 | #PC5.4-2.2-1 uses C_pc′ ≥ C_pc without citing its definition | Now "C_pc′ = C_pce^{40c_πα_{1,k+1}} ≥ C_pc", citing map #MD2.4.12.28 (read: "one factor C_pc′ := C_pce^{40c_πα_{1,k+1}} per piece") |
| 3 | The ς-endpoint convention for the merged step-(i−1) occurrences is not stated | #PC5.4-2.2: "The ς-step's run-B end takes the merged step-(i − 1) occurrences at c^0_{i−1}, as the wraps are held at run A's", with #PC4.14-1b.1.1 cited for c^0. This is #C7.6-6-4-5's convention |
| 4 | The order of the old-component removal and the t-step is not stated | #PC5.4-1.1 now says that each run's old components are removed first. They enter only the 𝐑-part through 𝐓′_i(X) (#C7.6-6-3, read), whose cross constant holds no carried insertion (#658). So the ς-step and the t-step compare the terms without old components |
| 5 | #PC4.4-1.2 adds the condition k ≥ k_W^× after the "least" definition | Merged into #PC4.4-1's list; #PC4.4-1.2 now only defines k_W^× |
| 6 | "Uniform in the volume" holds only through a period-free majorant | #PC5.4-3 is split. #PC5.4-3.1 says that the majorant is free of the torus period, since m_K enters only through L^{m_K} (#PC4.8-8.2, #PC4.12, #PC4.14-5.6), which #PC4.4 bounds with â_* ≥ min(a_×, 2c_w/M, a^cr_E). Checked: ρ^{E,×}_K uses C^E_r(kθ̃^kL^{m_K} + w_K), and #PC4.12's τ^{w,×}_K ≤ 28C_w(ℓ₁+ℓ₂)𝔟̄max(1, 4L log(K + 2)/â_*)(K + 2)^{−4} |
| 7 | #NL10.5 does not name the N-loop a priori Kotecký–Preiss half | #NL10.5 is split. #NL10.5-1 adds "with #NL6A.8's Kotecký–Preiss condition at the enlarged amplitudes for #PC5.4-2.2-2's a priori half". #NL6A.8 makes the per-position counts at most N_C/2 times the pair's, fixed before g |

Also changed, as bookkeeping with no change of mathematics:
- TL #590 now reads "𝒢 has at most 81Mσ positions, and C_S′ρ·pl ≤ ν/(64·81M)". The old wording put the product of the count and the amplitude under ν/(64·81M).
- Lines over 600 characters were split at sentence boundaries: #PC4.14.4-4 (new #PC4.14.4-4.0), #PC4.14.4-4.5.1-2 (new -2-1), #PC4.14.4-4.5.4-3-1 (new -3-1.1), #NL6A.7 (new #NL6A.7-1) and #NL9.6-5 (new #NL9.6-5-1).
- #NL.1's status words "Derived, not reviewed:" are deleted.
- Re-derived in the split lines: #NL9.6-5-1 gives 2^{N_C−1} sets T per i₀ and sup_n ne^{−10ηn/(LM)} ≤ LM/(10eη), so C′ = N_C2^{N_C−1}CLM/(10eη), which is 2CLM/(5eη) at N_C = 2.

Peer: the LF session's Cauchy #C7.8-9-9 repair (e46aa284d3da) was checked against #PC5.4-2.2 and agrees. R_EX_w = μ^{pt}; 81Mσ·ν_r/(5184M) = a°/2; Cauchy gives sup/(R − 1). One minor point was sent: R_E := ∞ is needed when Ȳ = 0.

## Pre-check: pc-wraps-20261109-r3 (9 Nov, 02:57)
- Round: full, on the same extracts, with #PC5.4-3.1 and #NL10.5-1 added.
- Changed lines under review: #PC4.4-1, #PC4.4-1.2, #PC5.4-1.1, #PC5.4-2.2, #PC5.4-2.2-1, #PC5.4-2.2-2.1, #PC5.4-3, #PC5.4-3.1, #NL10.5 and #NL10.5-1.
- Context lines that changed: #PC4.14.4-4, #PC4.14.4-4.0, #PC4.14.4-4.5.1-2, #PC4.14.4-4.5.1-2-1, #PC4.14.4-4.5.4-3-1, #PC4.14.4-4.5.4-3-1.1, #NL.1, #NL6A.7, #NL6A.7-1, #NL9.6-5 and #NL9.6-5-1 (splits only), TL #590 (wording), and the TL (6B)-a bookkeeping above (#609, #613, #613-2-1, #613-4–#613-7, #625, #728.1-1).
- Every changed line was re-read twice. The touched symbols k_W^×, C_pc′, c^0_{i−1}, â_* and Δ^{E,cr}_K were grepped:
  - k_W^× is defined only at #PC4.4-1.2;
  - #T12.3-5-1 is unchanged;
  - the table cites #PC5.4-3 for S^cr, which is still defined there.
- Quoted and checked:
  - map #MD2.4.13.4: "FV (5.10) for the tilted activities … so by FV (5.11)";
  - map #MD2.4.12.28: "C_pc′ := C_pce^{40c_πα_{1,k+1}}";
  - #C7.6-6-3: "multiply the operation 𝐓′_i(X) of every old component by 𝔷 … E°^R_i(0) is the step's 𝐑-part without old components";
  - #PC4.12's bound on τ^{w,×}_K;
  - #PC4.8-8.2's ρ^{E,×}_K.
- Directions checked: max(a, b + c) ≤ max(a, b) + c is not used here. â_* is a lower bound, so L^{m_K}'s bound is an upper bound.
- Lines over 600 characters in the pair note: none except #PC4.14.4-4.12 at 609. In NL: one, at 605.
- No known weak point is in the packet.
- SHAs: pair a2e8661e3fe3 (labels 9c22c0f93d08), TL 28ea9ffa219b (labels 991d3da45044), NL 4e915b6ed0f9, LF 8b6390bc65b9, table 72a5f3ad7918 (fork: W-δ and Cauchy rows only), Cauchy 6f7444fc6b1a.
- Launched 02:59 as btuzrxjf2. The reviewed blocks are 7.9k characters.

## Bookkeeping: TL (6B)-b definitions for tl-6bb-20261109-r1 (9 Nov, 03:01)
The definition check on spec_tl_6bb_r1 found 4 conflicts. All four are resolved by citing the one definition. None of these changes alters a bound, and none touches pc-wraps r3's lines (TL is context there, frozen in its snapshot).
- #656–#657: "Put E^{R×}_k := …" now reads "Since E_k^R(C;ℓ₀) = log(Ξ^c/Ξ) (15.4), #T4.52's E^{R×}_k is log Ξ^c_{12} − log Ξ^c_1 − log Ξ^c_2 + log Ξ". 15.4 was read: "E_k^R(C) = log(Ξ^c/Ξ)". The identity follows by subtraction, the three log Ξ's giving + log Ξ.
- #665: "with #T4.52's ḡ_R".
- #666: the derived bound is kept, followed by "which is #T4.52's C^{R×}_E". Re-derived: Σ_{m≥0}L^me^{−aL^m} ≤ e^{−a}(1 + 6/a) (#876) at a = ν_rD/(1024M), with 6/a = 6144M/(ν_rD).
- #670: "on ℐ(g), the union of the slots' bonds (#251)", which is #251's definition for a cross group.
- Consumers: PC #PC5.4 and #PC5.4-1 cite #657–#662 as the cross clusters, and NL cites #665–#666; all are unchanged. #T4.52's source column (#657, #665–#666) still points to the lines that derive these.
- Check: tl-6ba and tl-6bb, 0 conflicts each.
- SHAs: TL 28d97e2c6089, LABELS_TWO_LOOPS d8daae673528.

## Bookkeeping: TL (6B)-c definitions for tl-6bc-20261109-r1 (9 Nov, 03:06)
The definition check on spec_tl_6bc_r1 found 6 conflicts. They are resolved as follows, with no bound changed.
- #722 now reads "Take #T4.53's ε^r_k, ϑ_k, and λ_n at the 𝐑-steps". It restated the row before. Its uses were re-derived from the row:
  - #722's ϑ_k² = e^{−62δMR_k/512} ≥ e^{−63δMR_k/512};
  - #730's e^{−p₀/2} = (ε^r_k)²;
  - #722-1's λ_n ≥ 1 − S^R ≥ 31/32 under (H^R).
- #728.1 now reads "at the rate δ_α = min(1, (κ₁−1)/(4√d))" (D2.7 15.5(ii)'s) and "at #T4.30's rate δ = δ_α/M". The top line #9 now reads "δ = δ_α/M, #T4.30, #728.1".
- #728.3 now reads "#46's δ, δ₀/32, is #7's locality rate", and #728.4 "C_δ = 2 (#346)". Both are lists of other symbols, not definitions.
- #728.2: the exponent n := |𝒦| + 1 is written out as |𝒦| + 1, as #613-2-1 writes it.
- The LF moved to c3321e0e4802 (LF session), and the three TL specs' lf_sha are updated. Check: tl-6ba, tl-6bb and tl-6bc have 0 conflicts each.
- SHAs: TL 43786e4cb668, LABELS_TWO_LOOPS 2594ce98d883.

## Bookkeeping: TL (6B)-d definitions for tl-6bd-20261109-r1 (9 Nov, 03:09)
The definition check found 3 conflicts. They are resolved as follows, with no bound changed.
- #764 now reads "#T4.52's A^R_k sums e^{c_W}w_k(D_g^×) over the first-case groups", in place of "Put A^R_k := …".
- #774 now reads "*The smallness (H^R)* is #T4.53's: S^R ≤ 1/32 and C_yS^R ≤ log 2". It restated S^R's definition before.
- #776: the local u is renamed 𝔲, which occurs nowhere else; u clashed with #T4.42 and LF. Re-derived on the way:
  - e^{−p₀(g_k)/4} ≤ u_k^{−2} needs A₀(log u_k)^{p₀−1} ≥ 8, which is monotone in u_k ≥ 𝔲;
  - e^{−31δMR_k/512} ≤ u_k^{−2} needs δM log u_k ≥ 1024/31 ≈ 33.03 at r ≥ 2;
  - Σ_{n≥0}(𝔲 + bn)^{−2} ≤ 𝔲^{−2} + 1/(b𝔲).
- Spot-checked in the part (no change): #754-1's 4/34 ≤ 1/8 and 8/(512·34) ≤ 1/2048; #758's 20MD_P + 8Mℓ_P positions; #759's 21/4; #762's 1024·21/20 = 1075.2 ≤ 1076; #778's 13893312 = 12·1076².
- Check: tl-6ba through tl-6bd, 0 conflicts each.
- SHAs: TL fbf8377de25b, LABELS_TWO_LOOPS 172f74df2244.

## Bookkeeping: TL (6C) definitions for tl-6ca-20261109-r1 and tl-6cb-20261109-r1 (9 Nov, 03:15)
- #793 now reads "with σ_g (#691) in place of σ for a cross group and σ̃(D_g) (#826) for a group on one loop". The old "σ := …" clashed with the weight's σ, and heading names are replaced by tags.
- #844-2-1 now reads "at most 1 + c_r⁺ϑ_k²/(0.078eν_r) ≤ 1 + y^s_k ≤ 1 + C_ϑϑ_k, with #T4.53's y^s_k and C_ϑ … and by at most 1 + 4c_r⁺ϑ_k/(3eν_r) ≤ 1 + C_ϑϑ_k when it is two-loop". Re-derived: 1/0.078 ≈ 12.82 ≤ 13, ϑ_k ≤ 1, and 4/3 ≤ 13.
- #844-5 now reads "as #T4.53's C_att ≥ 2e^{−a}(1 + 1/a), since a ≥ ν_r/(32u_𝔏M) by D ≥ 1". Re-derived: 1/a ≤ 32u_𝔏M/ν_r.
- spec_tl_6ca_r1: #805-1, #812-0–#812-1, #814-1–#814-2-1 and #814-4-2-0–#814-4-2-2 are in balaban_proofs/BP_TL_SECOND_CLASS.md, which the spec now names in place of a TL extract.
- Banned-word grep over TL, PC and NL: "bridge" (D2.6 closure 5.5's term, #323, #494, #499, #844-4-1, PC #PC4.14.4-4.5.2-1) and "gap arc" (the map's term, #MD2.2.6.119) are existing mathematical usage, like "collar", and stay.
- Spot-checks in (6C)-a and (6C)-b, with no change: #795's 9/32; #799's 0.921875; #817's 8·5·1.02⁴ ≈ 43.3 ≤ κ; #823's e^{−7p₀/16}; #828's 21/4; #835's 21/80; #843-1's 4.03 ≤ 4.1; #842-1's 2e^{1/32} ≤ 4; #844-8's 26.4 < 5000; #845-1's 17/320 ≤ log 2; #855-1's 22/R_k² and 1.05/R_k; #858's 0.88958 ≤ 0.89.
- Check: all six TL part specs (6ba, 6bb, 6bc, 6bd, 6ca, 6cb) have 0 conflicts.
- SHAs: TL 1a893f402ae6, LABELS_TWO_LOOPS 172f74df2244.

## Triage: pc-wraps-20261109-r3 (9 Nov, 03:24)
Verdict: no fatal finding, one serious finding (S1) and six minor ones (m1–m6). The round is not clean, and the clean count stays 0.

Repairs (pair note, now db8057141d3c, LABELS_PAIR_CAUCHY 5bf0764d143f; NL 55f48cac1e6c):
| Finding | Repair | Tags |
|---|---|---|
| S1: the single-loop gases S°_{C_i} inside E^×_i were not shown to ride on the pair's interpolation; by (L×) their activities agree with the pair's only away from C_{3−i} | Each loop's gas is moved on its own data by the same two steps: the ς-step with run A's wraps held and the merged occurrences at c^{0,(i)}_{i−1}, then c^{t,(i)} = c^{0,(i)} + tδc^{(i)}. §4's bounds hold for these data with C := C_i at the pair's values, so the relative differences are at most ρ^{E,×}_K + x̄_K and δε̂^{(i)}_i ≤ D^{cw}_K. u₀ is taken with δε̂^∨_i, the largest of the three gases' δε̂_i, and r°(c^t) is the largest root sum. (L×) applied in run A, in run B and in the hybrid c^0 keeps the cancellation #444–#447 at every ς and t, as each step is affine. Δ^{E,cr}_K is unchanged | new #PC5.4-1.3, #PC5.4-1.3-1, #PC5.4-1.3-2; #PC5.4-2.2, #PC5.4-2.2-2, #PC5.4-2.2-2.1, #PC5.4-2.2-3, #PC5.4-2.2-4 |
| m1: K₁ should cover both loops; period uniformity of K₁^× not stated | K₁^× ≥ max(K₁(C₁), K₁(C₂)); #PC4.4-1.1 states that the added conditions' threshold is free of the torus period, through #PC4.4's bounds on L^{m_K} and e^{−â_*L^{m_K}} | #PC4.4-1, #PC4.4-1.1 |
| m2: D^{cw}_K also holds m_K + 1 and (ϖ^{cwd})^{m_K+1} | Named as increasing functions of L^{m_K}, with ϖ^{cwd} ≥ 1 (#PC4.14-5.5.0) | #PC5.4-3.1 |
| m3: the interpolation is #PC4.8-2.1's; the occurrences' majorants on the ς-disc were not stated | Cites #PC4.8-2.1; new #PC5.4-1.2-1 states that on this disc each x^ς stays within twice run A's bound at every young step, so the merged occurrences keep c̄^{(2)} | #PC5.4-1.2, #PC5.4-1.2-1 |
| m4: the conditions of the same kind were not named; (KP^{(2)}) gives the a priori half | #PC5.4-2 names (KP^{(2)}) for the T-part and D2.7 15.3 and #661 for the 𝐑-part; #PC5.4-2.2-2 derives a°/2 from ε̂^{(2)}_i ≤ ν_r/(5184M) = ν/(64·81M) | #PC5.4-2, #PC5.4-2.2-2 |
| m5: #NL6A.8 is an original-amplitude statement; #NL10.4-1 and #NL10.4-3 not cited | #NL10.5-1 cites #NL10.4-1's D^{cw}_K and #NL10.4-3's K_Q and (KP^{(2)}), and moves the N_C loop gases as in #PC5.4-1.3 with #NL5.3's cancellation | #NL10.5-1 |
| m6: #PC5.4-1.1's "so" joined two facts | Split: the removal leaves no old components for the ς-step; the t-step moves the T-part alone, as the 𝐑-part holds no carried insertion | #PC5.4-1.1 |

Re-derivations behind S1. The cancellation needs equal cluster weights at every point of both steps. A cluster of #444 has its network away from C_{3−i}. Its groups' activities are built from the constituents, wraps and occurrences in the network (#426–#428). (L×) makes these equal for the pair and for C_i at each end of each step: run A at ς = 0, the hybrid at ς = 1 and t = 0, and run B at t = 1. The steps are affine in their parameters, so the weights are equal at every ς and t. The single-loop data's sources are the pair's restricted to C_i (ℓ_i ≤ ℓ₁ + ℓ₂, no cross insertions), so #PC4.14-5's majorants, defined with equality from the sources, dominate them. 2/u₀ = c″δε̂^∨_i ≤ c″D^{cw}_K, so the t-step's bound is unchanged.

## Pre-check: pc-wraps-20261109-r4 (9 Nov, 03:24)
- Full round. Changed tags: #PC4.4-1, #PC4.4-1.1, #PC5.4-1.1, #PC5.4-1.2, #PC5.4-1.2-1 (new), #PC5.4-1.3, #PC5.4-1.3-1, #PC5.4-1.3-2 (new), #PC5.4-2, #PC5.4-2.2, #PC5.4-2.2-2, #PC5.4-2.2-2.1, #PC5.4-2.2-3, #PC5.4-2.2-4, #PC5.4-3.1, #NL10.5-1. In the context, TL #656, #657, #665 and #666 now cite #T4.52's E^{R×}_k, ḡ_R and C^{R×}_E in place of restating them (the TL (6C) bookkeeping above); each row was compared with the r3 text and is the same definition.
- Every changed line was re-read twice. One defect was found and fixed in the process: #PC5.4-2.2-4's u₀δε̂_i, now u₀δε̂^∨_i.
- Every use of u₀, δε̂_i, r°(c^t) and K₁ in §5 was grepped. u₀ of #PC4.14-1b.2 stays the pair gas's at the occurrences' step (#PC4.14-1b.3). §5's disc radius is renamed u₀^∨ := ν_r/(5184Mδε̂^∨_i) (#PC5.4-2.2), and every §5 use (#PC5.4-2.2-2, #PC5.4-2.2-3, #PC5.4-2.2-4) reads u₀^∨.
- The cited displays checked: #PC4.14-1.2's (KP^{(2)}); #PC4.14-5.5.0's ϖ^{cwd} = ϖ^{cw} + 1 + … ≥ 1; #C7.4-7-1–#C7.4-7-6 (K₁ of one loop); TL #413–#428 ((L×) and its per-object induction); NL #NL5.3 (the cancellation away from every other loop).
- Banned words cleared in the pair note's context lines: #PC4.14.4-4.5.4-8's "Z's collar" is now "each cube of Coll_k assigned to Z (D2.6 closure 2.0)", the assignment whose count 13^d gives #PC4.14.4-4.5.4-9; #PC4.14-4.3's "D26 closure 5.5's budget" is now "D26 closure 5.5, the share (ν_r/32)σ of a fixed member's e^{ν_rσ(W)}", the share 5.5 assigns to (12)(e)'s occurrence charge.
- Size of the reviewed blocks: 9,366 characters before, 9,600 in the built packet, block headers included (≤ 25k); every line is ≤ 600 characters.
- build_packet's definition check flagged "C := C_i" in #PC5.4-1.3 and #PC5.4-1.3-1 as a second definition of C. #PC5.4-1.3 now takes #PC4.14-1b.1's data "for the loop C_i alone", and #PC5.4-1.3-1 reads "§4's bounds, with the pair's majorants, hold for these data", which is what its reason (sources restricted from the pair's, ℓ_i ≤ ℓ₁ + ℓ₂, no cross insertions) gives; question 2 of the spec reads the same.
- The final full read of the reviewed blocks found two defects, fixed. (1) In #PC5.4-1.3–#PC5.4-1.3-2 the loop index i clashed with the step index i of §5 (δε̂^{(i)}_i, c^{t,(i)}); the loop is now C_q, q ∈ {1, 2}, also in #PC5.4-2.2's c^{t,(q)}, and #PC5.4-2.2-3 reads ℓ₁, ℓ₂, D ≥ 1. (2) #PC5.4-1.3-1's "(KP^{(2)}) is taken for S°_{C_q} too" now says why it holds: (KP^{(2)}) is a condition on the majorants c̄^{(2)} (#PC4.14-1.2), which dominate the loop gas's data by the same line, and #PC5.4-2.2-2 uses only that domination.
- spec_pc_wraps_r4: PC 0bf4e4fc61ea (LABELS_PAIR_CAUCHY 6482f7c8f7ce), NL 55f48cac1e6c, TL 1a893f402ae6, LF 407d8571498c. The context adds TL #411–#431, NL #NL10.4–#NL10.4-3, PC #PC4.14-5–#PC4.14-5.6, PC #PC4.8-1–#PC4.8-2.1 and PC #PC5.1–#PC5.3, and the claim and questions cover #PC5.4-1.3–#PC5.4-1.3-2 with u₀^∨.

## Bookkeeping: moved LF tags (9 Nov, 03:30)
The LF's #3.84–#3.90 moved, tags kept, to balaban_proofs/BP_LFR2_CHI_K_LAMBDA.md (c7167759d4de); the statement stays at LF #3.83-1. Re-pointed: BP_LFR2_REPLACEMENT #160.4-1-1 (BP #3.85.1–#3.85-1), #160.5 (BP #3.85-1), #160.5-1 (BP #3.84-1.1), #160.6 (BP #3.86), #160.6-2 (BP #3.86-1), now 0e3e3f3bff59; BP_TL_EVAL_POINTS #200 (LF #3.83-1 for χ_{k,Λ}), now e646589cf52f. No other file of this session cites #3.84–#3.90. Table fork: table 4ded6e9b630e, LABELS 53727d5fb133; c_T, renamed c_{av}, appears in none of this session's notes.

## Wording repairs applied (9 Nov, 03:41)
Each banned word is replaced by the object it names; no bound changes.
- TL: #262 and #844-2 cite #858, whose heading is now *D's weight*; #629-4's heading is *The links' weights*; #342's b_k is #T3.35's, with C_S″b_k the amplitude of a wrap group failing (i) or (iii) or of kind (γ) (D2.6 closure 2.1–2.2); #496 names D2.6 closure 5.5's split of e^{ν_rσ}, the share sh(D) of (6A)(i) (#564, #599), the unused merge-extent share and the other shares' (15/16)ν_rσ; #496.1 and #583 name the transports' share (ν_r/16)σ (map #MD2.4.11.5, #MD2.4.12.27); #598 names map #MD2.4.12.20-7's maximal subarc without intervals, of length ≤ |H_i(D″)| ≤ 4diam(S_{D″}), and splits off #598-1; #629-0-2 cites D26 §1 and 2.0 for Coll_j; #639 spends each cube's e^{−(κ₁−1)} as #640–#642 state; #670 says "the arcs of the loop between the intervals of ℐ(g)"; #794, #836, #839, #840 write Coll_k and Coll_{j₁}, and #836 names the bases (Coll_k in Case (a), W₁'s base in Case (b)); #799 says "the fraction of its weight's rate"; #844-4-1 cites #496 for the shares' (15/16)ν_rσ. "bridge" stays where it is D2.6 closure 5.5's defined path ((T3)). "gap arc", this note's own term, is now "joining arc", defined at #394 as the shorter of the two arcs between joined pieces (map #MD2.2.6.119), in #394, #395, #507, #552, #586, #597 and NL #NL3.4 (which now cites #394). TL now 64431e5df295, LABELS_TWO_LOOPS 76c232eb28af (1395 tags), NL 4628bb4847c7.
- BP_TL_EVAL_POINTS (b645a7a26446): the set called "step n's collar" had no definition. New #88.1.0 defines step n's integration set (Ω^c_{j+1}∖Z″_{j+1}) ∩ Z, j = h + n, where V_j is integrated under V̄_j = V_{j+1}, with 𝔹_k^{(n)}'s layer-j blocks and 𝔹_k^{(n+1)}'s layer-(j+1) blocks (LFR I p.180 l.4–6, l.18–22, (1.14)–(1.16); checked against (1.16) for 𝔹_k^{(j−h)} and 𝔹_k^{(j+1−h)}, whose layer-j sets differ by Ω^c_{j+1}∖Z″_{j+1}, as Z″_j ⊂ Z″_{j+1}). #88.1-3-1, #93-1, #97-2, #97.1, #97.1-1, #111 and #116-1 cite it; #97.1 no longer restates p.180. #78-3 cites #75-2's sum for the pre-R phase; #130.4-4, #137-1 and #166-4 name #138's bound on the response and #166-4's sum for the current; #166-3 says "the gradient's terms"; #130.15-1 names the slack 2^{−m−1}r_{ω,j} between consecutive radii and the constant of ρ_ω (#6.17.3-2–#6.17.3-3). Split for length: #88.1-3-1-1, #130.15-1-1. #88.1.0 is new mathematics: the TL part round whose context reads EVAL #88–#116 reviews it.
- BP_TL_GC_TRANSFORMS (20b66b534931) #6.17.1-2 and BP_TL_NSTEP_FRAME (ea8003fe9b15) #3.2.2-4: the same two replacements.
- The queued specs spec_tl_6ba_r1, spec_tl_6ca_r1 and spec_tl_6cb_r1 still use "budget" in their claims and questions; each is rewritten when its round is prepared.

## Pre-check: tl-6ba-20261109-r1 (9 Nov, 03:45)
- Full round, the first of (6B)-a, #607–#635 under review. Changed since the lines were split from the (6B) packets: #628-1-3–#628-1-3-1 (new), the tag citations in place of heading names, and today's repairs: #613-5 (CRE p.256 l.21–22 for the components being unions of MR_k-cubes, in place of LFR I p.177 l.17–19, which does not print it), #622 and #624 (#620's relation in place of "link", which #629-0 reserves for D2.7's X ∈ 𝔏), #628-1-1 split into #628-1-1-1, #629-0-2 (Coll_j cited to D26 §1 and 2.0), #629-4 (heading *The links' weights*).
- I read every line of #607–#635. Re-derived: #613-5–#613-7 (|S| ≤ 2^{d+2}ℓ/(MR_k) from #628-1-3 and ℓ ≥ MR_k; (δ/8)ℓ ≥ δMR_k|S|/2^{d+5}; the (e3^d)^n count; δMt_k ≤ δM + 2log α_{1,k}^{−1} + log(L⁴R_k²) from δ ≤ δ₀/32; −1/8 + 1/512 = −63/512; c_r and c_r⁺ as #T4.53 states); #613-6's 3^d#_k + 2^dn_k ≤ 3^d(3^d + 2^dM)(#_k + n_k/M) and (21/20)σ + 17 ≤ 18.05σ; #628-1-3 (⌈2ℓ/t⌉ ≤ 2ℓ/s + 2 for t ≥ 2ℓs/(2ℓ + s); a set of extent < s meets ≤ 2 closed intervals per coordinate); #629-2-1, #629-2-3, #629-2-4 (k ≥ 3, L^{k−1} ≥ L², runs of L² cubes, L² ≥ 2A_E); #629-4-0 (1/640 + 1/1458 + 1/1024 < 1/256); #629-4-1 (3/1024 ≥ 1/512); #629-5 (640·72 = 46080); #630, #631, #633 (+4R_k, +2, +88).
- Pins checked against the corrected transcriptions: LFR II p.373 l.15, l.33, p.374 l.10, l.28, p.376 l.10–13, l.39, p.387 l.42, p.388 l.2–3, l.29; CRE p.245 l.38–43, p.256 l.21–22, p.264 l.54–55; REG p.098 l.20–21; RG I p.257 l.7–16; LFR I p.177 l.33–34.
- Symbols grepped against the table: c_r, c_r⁺, C_α, t_k, δ (#T4.53, #728.1), λ_𝔏, ℓ_P (#T4.42), C_box (#T4.44), c_g = 0 (#T4.51); no restated row.
- spec_tl_6ba_r1: TL 0b3fb8217b61 (LABELS_TWO_LOOPS 305bfa222086), LF 407d8571498c; definition check 0 conflicts. The claim, caller and question 4 no longer say "budget". Launch after pc-wraps-20261109-r4 is triaged; size measured at the build.

## Pre-check: tl-6bb-20261109-r1 (9 Nov, 03:55)
- Full round, the first of (6B)-b, #636–#689 under review. Changed: #637, #637-1 (#628-1-3), #639 (the split of each cube's e^{−(κ₁−1)}), #644, #648, #649, #652-1 (LFR II p.389 pinned by corrected-transcript line in place of "the n-th line below (1.94)"), #649 (quotes Bałaban's assumption −2(1+β₀)^{−1}p₀ + 1 + 2κ(100R_k)^d ≤ −(3/2)p₀, p.389 l.14–18), #655 (2κ(100R_k)^d < p₀/2 derived from it, since 2/(1+β₀) − 3/2 < 1/2 for β₀ > 0), #657, #665, #666 (#T4.52), #670 (arcs between the intervals of ℐ(g)).
- I read every line of #636–#689. Re-derived: #637 (2^{d+1}(d_k/R_k + 1) ≤ d_k + 2^{d+1} for R_k ≥ 2^{d+1}), #637-1 (βκ/8 ≥ 3·2^{d−2} from βκ ≥ 6·2^d), #638 (3δM/4 = 3/4 = (3/2)c_F^× at δM = 1), #642 ((2L−1)κ ≥ 2), #644 (the p.376 l.5–6 inequality fails for β ≥ 1), #648 (M^{−d}|·| and (MR_k)^{−d}|·| per π_k-cube; a_V ≥ βκ/(12·2^d) ≥ ½), #651 (e^{−(3/2)p₀} less (1.96)'s e^{−p₀/2}), #654 ((104R_k + 88)^d ≤ (105R_k)^d for R_k ≥ 88), #655 (2ν_r(1.05)^d(100R_k)^d ≤ 2κ(100R_k)^d/8 < p₀/16, times 5/4 = 5p₀/64), #660 (𝔅(P) = ∅ at the flat reference, #658, so diam ≤ M(D_P + 2ℓ_P) and the chain gives DL^m/M), #662 (≤ 2·4ℓ_iL^m ≤ 2^d·4ℓ_iL^m cubes on C_i, four gases: 2^{d+4}), #666 (#876 at a = ν_rD/(1024M): 6/a = 6144M/(ν_rD)), #673, #678 (D2.7's hull(g) := span(g) ∪ ∪_{P∈g}dom P, D2.7 l.169).
- Pins checked against the corrected transcriptions: LFR II p.355 l.11, p.376 l.5–6, l.34–39, p.378 l.14–15, p.389 l.12–41, p.390 l.1, p.391 l.15–18; LFR I p.177 l.26, l.32–33; RG II p.5 l.6–8, p.20 l.17.
- #685's pin of c₁ = α^{1/3} is p.390 l.2 of the corrected transcript (l.1 is its comment line).
- spec_tl_6bb_r1: TL 9450a26e95c5 (LABELS_TWO_LOOPS 05cbbf9b11e2), LF 18e8006d1dc5; spec_tl_6ba_r1 updated to the same SHAs. Launch after tl-6ba-20261109-r1; SHAs re-checked at the build.

## Triage: pc-wraps-20261109-r4 (9 Nov, 04:12)
Verdict: no fatal finding, one serious finding (S1) and six minor ones (m2–m7 in the review's numbering). The round is not clean, and the clean count stays 0.

Repairs (pair note, now 0091563d6522, LABELS_PAIR_CAUCHY db12844afef9, 340 tags; NL 251b74ca0ee6):
| Finding | Repair | Tags |
|---|---|---|
| S1: at the first young step i₀ the merged step-(i₀ − 1) occurrences are built at an old step; the ς-step cannot reach c^0_{i₀}, whose occurrences have run B's old-step constituents | The fresh part holds at run A's, with the carried wraps, the step-(i₀ − 1) occurrences that the groups with a wrap member hold. c^0's occurrences at i₀ are those, so at the young steps c^0 is exactly the end of the ς-step; its old-step definition is unchanged. In δε̂_{i₀} the second change (run B's to run A's step-(i₀ − 1) occurrences) touches only the groups with a wrap member, the dev groups being dev insertions compared whole; their wrap members are old, run A's, of weighted mass ≤ τ^{w,×}_K, and the factor 3 per member gives ≤ 6C^{ε̂}τ^{w,×}_K. So the recursion starts at 3C^{ε̂}τ^{w,×}_K ≤ 12C^{ε̂}τ^{w,occ}_K, inside the existing start G_{i₀−1}; D^{cw}_K, B^H_K and Δ^{E,cr}_K are unchanged. §5's ς-step holds the same occurrences, and its run-B end is this c^0 | #PC4.14-1.4 (i₀ cited from #T4.55), #PC4.14-1b.1.1, new #PC4.14-1b.4.2-1–#PC4.14-1b.4.2-2, #PC4.14-4, #PC4.14-5.5-1, #PC4.14-5.5.0.1, #PC4.14-5.5.2, #PC5.4-1.2, #PC5.4-1.2-1, #PC5.4-1.3, #PC5.4-2.1, #PC5.4-2.2 |
| m2: (KP^{(2)}) as defined is a sup over the pair's gas and does not cover S°_{C_q}; the same for r°(c̄^{(2)}) ≤ C_S′𝔞̄ | (KP^{(2)}) is required of each of the three gases, ε̂^{(2)} over the gas's own groups; the map's count is per position and one loop's for S°_{C_q}; the root sum uses the pair's C_S′, which bounds one loop's count (TL #591). #PC8.1.1 and NL #NL10.4-3 list it for each gas | new #PC5.4-1.3-1.1, #PC5.4-2.2-3.1, #PC8.1.1, #NL10.4-3 |
| m3: "restricted to the wraps and insertions of C_q" | §4's recursions run with C_q's own sources, each at most the pair's: ℓ_q ≤ ℓ₁ + ℓ₂, no cross insertions, one loop's per-position counts (TL #591) | #PC5.4-1.3-1 |
| m4: "each step being affine" does not cover the recomputed occurrences | The constituents and c^t agree by affinity with agreeing ends; the occurrences agree by induction over the steps from those held at i₀, run A's | #PC5.4-1.3-2, new #PC5.4-1.3-2.1 |
| m5: #PC4.4-1.1 cites #PC5.4-3.1 for e^{−â_*L^{m_K}} ≤ (K + 2)^{−4} | Cites #PC4.4 | #PC4.4-1.1-2 |
| m6: period-freeness shown only for m_K | The period enters only through c_wN_s/M (PC #PC4.4, TL #893–#894, w̄^{(2)} #PC4.13-4; no other N_s in PC or TL); w_K, s_K, r^V_K, η^{gen}_K are built from K, k, θ̃ and constants; the rate enters m_K and the wrap tails, bounded through â_*, and w̄^×, w̄^{(2)}, which decrease in it and are at most their values at N_s = 2 | #PC4.4-1.1, new #PC4.4-1.1-1–#PC4.4-1.1-2, #PC5.4-3.1 |
| m7: for N loops K₁^× ≥ max_iK₁(C_i) not stated | Stated | #NL10.4 |

Re-derivation of S1. A step-i₀ group holds step-(i₀ − 1) occurrences only through members present at the step i₀ − 1 (#PC4.14.1, #PC4.14-4), all made at old steps (#PC4.14-2). The reference groups' carried insertions are the dev ones, marked activities interpolated whole, and the wraps (#PC4.14.4); on a dev member the occurrences are part of a dev insertion, compared with it (#PC4.14-2.3). So the occurrences outside the marked activities sit in groups with an old wrap member, linear in it. Holding them at run A's makes the ς-step's end, recursively from i₀, the redefined c^0, which #PC4.14-6.2's step c^0 → c^{w0} (wrap groups at run A's) also needs. The t-step from c^0 to c^B then pays the old-step part by absolute masses: |c^B-occ value| + |c^A-occ value| ≤ 2·3C^{ε̂}W^A_{i₀}, W^A_{i₀} ≤ Σ_{j≤K′−m_K}t_{K′−j} = τ^{w,×}_K (#PC4.14-1b.7.3). Since τ^{w,×}_K = Σ_{m≥m_K}t_m ≤ Σ_{m≥m_K}2^mt_m = τ^{w,occ}_K, the start 3C^{ε̂}τ^{w,×}_K is below 12C^{ε̂}τ^{w,occ}_K, so H^{cw}_{i₀−1} ≤ B^H_K stands and every later bound is unchanged. The attached births at i with i − 1 ≤ k − m_K (#PC4.14-4.6.4) use the old-step c^0, whose definition and bound #PC4.14-1b.7–#PC4.14-1b.8.1 are unchanged.

Rechecks. Every changed line was re-read twice after the edits. Second pass: #PC5.4-2.1's "at run A's wraps" now reads "between run A and c^0"; #PC4.14-1b.4.2-1's first sentence no longer repeats "the groups with a wrap member"; #PC4.14-1b.4.2-2 names the sum of the two values. Lines over 600 characters split: #PC5.4-1.3-1 (.1), #PC5.4-1.3-2 (.1), #PC5.4-2.2-3 (.1); #PC5.4-2.2 is 606. Consumers grepped: #PC4.14-1b.8.1 (now cited only by the old steps' lines), #PC4.14-5.5-1, c^0 in #PC4.14-3a.2.1–#PC4.14-3a.2.2, #PC4.14-4.2, #PC4.14-4.6.4, #PC4.14-6.2; NL #NL10.4-1, #NL10.5-1. Peer messages: table 530c9da5a4de (c_{av} ≥ 4d, unused here), LF d72f4de24c38 (text only; BP_LFR2_CHI #3.86-1.1 deleted, cited by none of this session's files).

## Pre-check: pc-wraps-20261109-r5 (9 Nov, 04:20)
Full round of the same extracts as r4, with #PC4.14-1.4, #PC4.14-1b.1–#PC4.14-1b.1.1, #PC4.14-1b.4–#PC4.14-1b.4.2-2, #PC4.14-4, #PC4.14-5.5-1 and #PC8.1.1 under review, and with TL #749 and #893–#894, #PC4.13-4 and #PC4.14.1–#PC4.14.4 added as context. Notes: PC 0091563d6522 (340 tags), TL 6efa48e72168, NL 251b74ca0ee6, LF d72f4de24c38, table 530c9da5a4de. Reviewed blocks 17,665 characters; argument 54,879.
- Second recheck of the r4 repairs. #PC4.14-5.5-1 had dropped the old-step bound: e^{cw}_{i₀}'s recursion carries c″S^{(2)}δε̂_{i₀−1} with the actual δε̂_{i₀−1} (#PC4.14-5.4), and only δε̂_{i₀}'s recursion takes 3C^{ε̂}τ^{w,×}_K in its place. It now states both: δε̂_{i₀−1} ≤ 12C^{ε̂}τ^{w,occ}_K (#PC4.14-1b.8.1) and 3C^{ε̂}τ^{w,×}_K ≤ 12C^{ε̂}τ^{w,occ}_K, so G_{i₀−1} ≤ 12C^{ε̂}τ^{w,occ}_K in both recursions; B^H_K is unchanged. #PC4.14-1b.4.2-2 now ends "#PC4.14-1b.4's recursion holds at i₀ with 3C^{ε̂}τ^{w,×}_K in place of δε̂_{i₀−1}", the comparison with τ^{w,occ}_K stated once, in #PC4.14-5.5-1; "at either occurrences" reads "with either run's occurrences". The claim (b) was corrected to match.
- #PC5.4-2.2: the later occurrences are built from the held data and run B's fresh constituents; the sentence "Move the T-part's activities along …", which defines u₀^∨, is split off as #PC5.4-2.2-0 (612 characters before). Only #PC5.4-2.1 cites #PC5.4-2.2, for c^0, which stays there; u₀^∨ is in no table row.
- Definition check: c^t in #PC4.14-4.2 cites #PC4.14-1b.1's; #NL10.4 and #NL10.4-4 write "⊔_iC_i for C"; i₀ is #T4.55's row, cited at #PC4.14-1.4 and #PC4.14-5.5-1, whose source range #PC4.14-5–#PC4.14-5.5.0 contains #PC4.14-5.5-1. 0 conflicts.
- Checked against the sources: τ^{w,×}_K = Σ_{m≥m_K}t_m (#PC4.12, t_m of #PC4.14-1b.7.3) ≤ τ^{w,occ}_K = Σ_{m≥m_K}2^mt_m (#PC4.14-1b.8); #PC4.14-1b.4's δε̂_i ≤ 3C^{ε̂}Δ^w_i + 2δε̂_{i−1}, the second term the second change, which at i₀ is ≤ 6C^{ε̂}τ^{w,×}_K = 2·3C^{ε̂}τ^{w,×}_K; #PC4.14-1b.6 and #PC4.14-5.5.0.1's B^H_K ≥ 12C^{ε̂}τ^{w,occ}_K; #PC4.14-6.5's F at the old steps, unchanged since dev groups are compared whole.
- Lines: none of the changed lines exceeds 600 characters (#PC4.14.4-4.12, 609, unchanged).
- Changed since r4, all re-read twice (28): #PC4.4-1.1, #PC4.4-1.1-1, #PC4.4-1.1-2, #PC4.14-1.4, #PC4.14-1b.1.1, #PC4.14-1b.4.2-1, #PC4.14-1b.4.2-2, #PC4.14-4, #PC4.14-4.2, #PC4.14-5.5-1, #PC4.14-5.5.0.1, #PC4.14-5.5.2, #PC5.4-1.2, #PC5.4-1.2-1, #PC5.4-1.3, #PC5.4-1.3-1, #PC5.4-1.3-1.1, #PC5.4-1.3-2, #PC5.4-1.3-2.1, #PC5.4-2.1, #PC5.4-2.2, #PC5.4-2.2-0, #PC5.4-2.2-3, #PC5.4-2.2-3.1, #PC5.4-3.1, #PC8.1.1, #NL10.4, #NL10.4-3; also #NL10.4-4 (context, wording only).
- Message to the table session: #T12.3-3's c^0 ("c at run A's carried wraps and run B's fresh constituents") is the old-step c^0; at the young steps #PC4.14-1b.1.1 holds also the step-(i₀ − 1) occurrences of the groups with a wrap member at run A's.
- Table session's reply: #T12.3-3 carries the young-step clause, citing #PC4.14-1b.1–#PC4.14-1b.1.1, and the row's second half is now #T12.3-3-1. Every cited #PC tag exists at 0091563d6522. Asked for rows for δε̂^∨_i (#PC5.4-1.3-1.1) and u₀^∨ (#PC5.4-2.2-0). After r5 the note will cite them instead of defining them with ":=".
- The rows are in, checked against #PC5.4-1.3-1.1 and #PC5.4-2.2-0: #T12.3-5-2 (δε̂^∨_i, with NL #NL10.5-1's N_C + 1 gases) and #T12.3-5-3 (u₀^∨). Table 5e201eef219c, LABELS a2a0ce7a86c6, LF 0e775f559e33. Queued for after r5: #PC5.4-1.3-1.1 and #PC5.4-2.2-0 cite #T12.3-5-2 and #T12.3-5-3 instead of defining them, and the next specs use the current LF.
- After LF packet 50 (e^{−c(M)} = exp(−O(1)log M abs(Λ))): table 4880d9abe6dd, LABELS c456056f4ec3, LF ead9ce05e514, Cauchy 320fada2a056. c(M) occurs in none of TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT. Every LF and table tag that TL, PC and NL cite exists in the new labels. Next specs use LF ead9ce05e514.

## Triage: pc-wraps-20261109-r5 (9 Nov)
Verdict: no fatal finding, one serious (S1) and five minor (m2–m6). Not clean; the clean count stays 0.

Repairs (pair note e636cc081bd1, LABELS_PAIR_CAUCHY a985a44370fc, 345 tags; NL 251b74ca0ee6 unchanged):
| Finding | Repair | Tags |
|---|---|---|
| S1: the young cross births at i₀ take in step-(i₀ − 1) occurrences on old dev members; their part c^A → c^0 at the old step is bounded nowhere | Every young cross or wrap birth at i₀ is split at #PC4.14-6.3's runs c^{nw,X}: the wrap-free occurrences are clusters of dev groups, interpolated with the birth's ς in the fresh part; each run's wrap part moves along t, ≤ c″η^{d,X}_{i₀−1} times the birth's bound; the births add c″δε̂^d_{i₀−1}S^{(2)} ≤ 16c″C^{ε̂}τ^{w,occ}_KS^{(2)}. G_{i₀−1} ≤ 16C^{ε̂}τ^{w,occ}_K, B^H_K's 12 → 16 | new #PC4.14-4.5-1–#PC4.14-4.5-4, #PC4.14-4, #PC4.14-2.1, #PC4.14-2.3, #PC4.14-5.5-1, #PC4.14-5.5.0.1, #PC4.14-6.1.2-4; table #T4.55 (requested) |
| m2: #PC4.14-1b.1.1's "computed at the previous step's c^0" holds only for the groups with a wrap member | Restricted to them; a dev group's activity is run B's whole | #PC4.14-1b.1.1 |
| m3: C_q's majorants at most the pair's asserted | The recursions are linear with nonnegative coefficients built from L, M, ν_r, e^{c_W}, C^{ε̂}, c″, S^{(2)}, (8.3)'s Bałaban terms and R_i (coupling and steps only: y^R_k = C_yε^r_k, #893); coefficients, sources and start for C_q at most the pair's; induction | #PC5.4-1.3-1, new #PC5.4-1.3-1-1 |
| m4: (KP^{(2)})'s satisfiability by analogy | ε̂^{(2)}_i ≤ twice #MD2.4.12.38-1's (ii-w) c-version sum at κ − κ_I, small for g small under the κ thresholds as the map's ε̂ is; (KP^{(2)}) once that sum ≤ ν_r/(10368M) | #PC4.14-1.2 |
| m5: #C7.6-6-4-5 holds the wraps only | Cited for the wraps; the occurrences are held with them by #PC4.14-1.4 | #PC5.4-1.2 |
| m6: K₁(C_i)'s period-uniformity not addressed | #PC4.4-1.1 names the single-loop wrap rates' lower bound a₀ (#CP.22-5-1); the remaining conditions of #C7.4-7 sent to the LF session, owner of the Cauchy note | #PC4.4-1.1 |
Also: #PC5.4-1.3-1.1 and #PC5.4-2.2-0 cite #T12.3-5-2 and #T12.3-5-3; #PC4.14-4.3 and #PC4.14-5.5.0.1 cite #T4.55's u₀ and B^H_K (definition check).

Re-derivation of S1. A young birth Y at i₀ depends on the step-(i₀ − 1) activities c in its occurrences and on its other constituents X. Y(X^A, c^A) − Y(X^B, c^B) = [Y(X^A, c^A) − Y(X^A, c^{nw,A})] + [Y(X^A, c^{nw,A}) − Y(X^B, c^{nw,B})] + [Y(X^B, c^{nw,B}) − Y(X^B, c^B)]. Without wraps the occurrences are dev clusters (#PC4.14-6.3.1); the dev groups' activity differences are the marks ≤ d^{ins}_{i₀−1} of #C8.3.3-4-3, covered as the marked activities are (#PC4.14-6.7), so the middle bracket is in the ς-step. For an outer bracket, c^{nw,X} + t(c^X − c^{nw,X}) has its end c^{nw,X} within c̄^{(2)} (wrap groups' activities 0 by multilinearity) and η^{d,X}_{i₀−1} ≤ 8C^{ε̂}τ^{w,occ}_K ≤ ν_r/(10368M) (#PC4.14-6.3.2), so u^X := ν_r/(5184Mη^{d,X}) ≥ 2 and Cauchy gives 2/u^X = c″η^{d,X}. The sum over X is c″δε̂^d_{i₀−1}. The occurrences on old cross or wrap members are covered by the same split, so #PC4.14-2.1's take-in clause is replaced. H^{cw}_{i₀−1} ≤ 16C^{ε̂}τ^{w,occ}_K + 64c″C^{ε̂}(1 − L^{−β′})^{−1}τ^{w,occ}_K = B^H_K. #PC4.14-6.6 (δε̂^d_{i₀−1} ≤ 16C^{ε̂}τ^{w,occ}_K ≤ B^H_K) and #PC4.14-6.7.1 (x_n ≤ 2B^H_K ≤ x̄_K, as D^{cw}_K ≥ 1024B^H_K) stand. D^{cw}_K's formula is unchanged in form.

Rechecks. Every changed line re-read twice. Second pass: #PC4.14-4.5-3 split (617 → #PC4.14-4.5-4); #PC4.14-6.1.2-4 keeps "carried part"; #PC4.14-1.2 reworded so that ε̂^{(2)}_i is the map's ε̂ at the enlarged amplitudes and the lowered decay, and the earlier draft's "5184 = 2·2592" (which suggested the wrong factor) is gone; #PC5.4-1.3-1's coefficient list includes e^{c_W} and (8.3)'s Bałaban terms. Consumers grepped: #PC4.14-4.5 (#PC4.14-5.4, #PC4.14-6.1.2-4), #PC4.14-2.1/-2.3 (#PC4.14-1b.4.2-1, #PC4.14-4), B^H_K (#PC4.14-5.5.0.2, #PC4.14-6.5, #PC4.14-6.6, #PC4.14-6.7.1, NL #NL10.4-5, table #T4.55, #T12.3-x), "12C^{ε̂}τ^{w,occ}_K" (#PC4.14-1b.6 and #PC4.14-1b.8.1, the old-step bound, unchanged). Peer messages: table session (B^H_K 12 → 16 in #T4.55, with the re-derivation); LF session (K₁(C)'s period-uniformity in #C7.4-7).

## Pre-check: pc-wraps-20261109-r6 (9 Nov)
Full round (the clean count is 0). Under review: r5's extracts plus #PC4.14-1.2, #PC4.14-2–#PC4.14-2.3, #PC4.14-4–#PC4.14-4.5-4, #PC4.14-5.5.0.1 and #PC4.14-6.1.2-4; context adds #PC4.14-6–#PC4.14-6.7.1 and TL #774–#775. LF ead9ce05e514; spec claim (a)–(h) and four questions rewritten for the repairs. Table bc802919cd0f has #T4.55's B^H_K = C^{ε̂}(16 + 64c″(1 − L^{−β′})^{−1})τ^{w,occ}_K; the table session re-derived it (η^d ≤ 8C^{ε̂}τ^{w,occ}_K per run, 1 − θ_o = (1 − L^{−β′})/2). Pair e636cc081bd1, labels 6cbc4ef6051b. Definition check 0 conflicts. Reviewed blocks 24,186 characters; argument 61,449.
- After launch: table 45c44724a314, LABELS feea5cc113fe, LF 31538d03f6ab, Cauchy 646ef7ef1bb6 (the chain's average is RG I (0.4) throughout; #T12.7, #T12.7-7, #T12.7-24, #T12.7-25, #T12.10, #T12.13 updated, c_Q = 10(d + 1)c_{av}). None of TL, PC, NL, BC or BP_LFR2_REPLACEMENT uses these rows or c_Q; BP_TL_EVAL_POINTS cites #T12.13-1 for c_π, which is unchanged. Next specs use LF 31538d03f6ab.
- LF session on r5's m6, Cauchy 1b66a27cdc01: μ₀ is now taken at a₀ (#C7.8-9-3, read: "μ₀ := C^w_Mρ̂^w_γT_w(a₀)", with T_w decreasing and a_w ≥ a₀), and new #C7.4-7-5-2 (read) states that K₁ does not depend on T_ph/u: the period enters only through a_w and a^{w,2}, by decreasing functions, each condition holding with a₀. Queued for after r6, since #PC4.4-1.1 is under review: #PC4.4-1.1 cites #C7.4-7-5-2 for max(K₁(C₁), K₁(C₂)) being free of the period, so that all of K₁^× is.
- BP_LFR2_REPLACEMENT #160.5-1 now cites "the chain's average RG I (0.4) (BP #3.84-1.1)" for CMP98 (15); #3.84-1.1 (BP_LFR2_CHI_K_LAMBDA, read) cites #C11b.2-4 for RG I (0.4). Citation only. No other "CMP98 (15)" in TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT.
- Table 432d40ec40a5, LABELS c9390a7d6154, Cauchy 1b66a27cdc01: #T4.40's μ₀ at a₀, #T12.7-4 notes #C7.4-7-5-2. μ₀ occurs in none of TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT; PC's only #T4.40 citation (#PC4.2-2.2) is for τ^w_K and D^{w,LF}_K, unchanged.

## Triage: pc-wraps-20261109-r6 (9 Nov, 05:17)
Verdict: no fatal and no serious finding; eight minor (m1–m8). Claim (a)–(h) confirmed. Not clean; the clean count stays 0.

Repairs (pair note 2786c825ab52, LABELS_PAIR_CAUCHY f44f17d83997, 346 tags; TL 6efa48e72168 and NL 251b74ca0ee6 unchanged):
| Finding | Repair | Tags |
|---|---|---|
| m1: #PC4.14-5.5-1 cites #PC4.14-4.5-3 for the 16 | Cites #PC4.14-4.5-4 | #PC4.14-5.5-1 |
| m2: #PC4.14-1.2 omits the weight constant C^{ε̂} | ε̂^{(2)}_i ≤ 2C^{ε̂} times (ii-w)'s c-version sum (#PC4.14-1b.4.5); threshold ν_r/(10368MC^{ε̂}) | #PC4.14-1.2 |
| m3: #PC4.14-4.5-1's "constituents are not interpolated" against #PC4.14-4.6's interpolation at old steps; the ς = 1 end at old steps unstated | #PC4.14-4.5-1: the pair's gas is not interpolated at the old steps (#PC4.14-1.4). #PC4.14-4.6: for i − 1 > k − m_K the attached birth's occurrences have #PC4.14-4.1's fresh and #PC4.14-4.2's carried parts; for i − 1 ≤ k − m_K they are split as in #PC4.14-4.5-1 (#PC4.14-6.3 holds at every old step), the middle difference in the fresh part. #PC4.14-4.6.4: the outer differences add c″δε̂^d_{i−1} ≤ 16c″C^{ε̂}τ^{w,occ}_K ≤ c″D^{cw}_K, so #PC4.14-4.7's c̄^{W,×}_K is unchanged | #PC4.14-4.5-1, #PC4.14-4.6, #PC4.14-4.6.4 |
| m4: r^E_{k−m_K} ≤ ρ^{E,×}_K used, stated only for i > k − m_K | #PC4.8-8.2's range is k − m_K ≤ i ≤ k; #PC4.14-4.5-2 cites it | #PC4.8-8.2, #PC4.14-4.5-2 |
| m5: δc read as c^B − c^0 | δc_𝒢 := c^B_𝒢 − c^0_𝒢, moving the carried wraps and the occurrences c^0 holds; #PC4.14-4.2 moves the occurrences' activities along it | #PC4.14-1b, #PC4.14-4.2 |
| m6: "free of the loops" overstated; #PC4.4-1.1-1's list omits k_W^× and K_Q | The pair's numbers, S°_{C_q} being split at the pair's i₀ (#PC5.4-1.3, #T4.55); #PC4.4-1.1-1 names k_W^× and K_Q (#PC4.4-1.2, #PC4.14-3) | #PC5.4-1.3-1-1, #PC4.4-1.1-1 |
| m7: #659's cancellation along ς not stated | #PC5.4-1.3-2 names #659; new #PC5.4-1.3-2-1: such a cluster has the same polymers, c_g and compatibility in the two gases #659 pairs, its activities built from the same constituents and C_q's bonds (#658); #PC5.4-1.3-2.1 then applies | #PC5.4-1.3-2, #PC5.4-1.3-2-1 |
| m8: the age split listed as a condition | Dropped from #PC8.1.1; (KP^{(2)}) for each gas cites #PC5.4-1.3-1.1 | #PC8.1.1 |
Also (queued): #PC4.4-1.1 cites #C7.4-7-5-2 (read: K₁ does not depend on T_ph/u, each condition holding with a₀) for max(K₁(C₁), K₁(C₂)), replacing the a₀ remark.

Re-derivation of m3. Attached births at i ≥ j₀ with i − 1 ≤ k − m_K take in step-(i − 1) occurrences at an old step, where the pair's gas is not interpolated. Split Y(X^A, c^A) − Y(X^B, c^B) at c^{nw,X} as at i₀. Middle: the wrap-free occurrences are dev clusters at every old step from j₀ − 1 on (#PC4.14-6.3.1), marks ≤ d^{ins}_{i−1}, their o-part ≤ x_i ≤ 2B^H_K ≤ x̄_K (#PC4.14-6.7.1); with the fresh constituents interpolated in ς, #PC4.14-4.6.1–#PC4.14-4.6.3 bound it (LF #5.38.2, ρ^{j₀}_K at i = j₀). Outer: η^{d,X}_{i−1} ≤ 8C^{ε̂}τ^{w,occ}_K ≤ ν_r/(10368M) (#PC4.14-6.3.2), so u ≥ 2 and each is ≤ c″η^{d,X}_{i−1}; sum c″δε̂^d_{i−1} ≤ 16c″C^{ε̂}τ^{w,occ}_K ≤ c″B^H_K ≤ c″D^{cw}_K (#T4.55; D^{cw}_K ≥ 1024B^H_K, ϖ^{cwd} ≥ 1, #PC4.14-5.5.1). #PC4.14-4.7's per-birth term c″D^{cw}_K + 8x̄_K covers both cases. m4: for k − m_K ≤ i ≤ k, iθ̃^i ≤ kθ̃^{k−m_K} = kθ̃^kθ̃^{−m_K} ≤ kθ̃^kL^{m_K/3} ≤ kθ̃^kL^{m_K}, so r^E_i = C^E_r(iθ̃^i + w_K) ≤ r̄^{E,×}_K. m2: 2C^{ε̂}·ν_r/(10368MC^{ε̂}) = ν_r/(5184M).

Rechecks. Every changed line re-read twice in context (#PC4.14-4–#PC4.14-4.7, #PC5.4-1.3–#PC5.4-1.3-2.1). #PC5.4-1.3-2 reached 607 characters and was split (→ #PC5.4-1.3-2-1). Consumers grepped: δc (#PC4.8-3.1's and #PC4.14.4-4.5.x's C_δc̄ are another symbol; #PC4.14-1b.1, 1b.2, 1b.7.1, 4.2, 6.2, #PC5.4-1.3, 5.4-2.2-0, 2.2-1.1, 2.2-2 read with δc = c^B − c^0, consistent; table #T12.3-3 defines c^t and c^0 only); (KP^{(2)})'s threshold (no table row; #PC5.4-1.3-1.1 cites #PC4.14-1.1–1.2); #PC4.8-8.2's range (#PC4.8-2.1 uses i > k − m_K, unaffected); "free of the loops", "not interpolated", "age split at" (none left). NL has no δc. Table fork messages: #T12.7-25 c_{av} and ρ_𝔤, #T12.7-25-1 (148b0683b464), and #T10.51's heading (13b7fe003c42, LABELS 0b06683b0273); none of TL, PC, NL, BC or BP_LFR2_REPLACEMENT uses #T12.7-25, c_{av} or #T10.51.

## Pre-check: pc-wraps-20261109-r7 (9 Nov, 05:20)
Full round (the clean count is 0). Under review: r6's extracts, with #PC4.14-1b, #PC4.8-8.2 and #PC4.14-4.6–#PC4.14-4.6.4 added; context adds #PC4.14-4.7–#PC4.14-4.7.1.1. Changed since r6 (15): #PC4.4-1.1, #PC4.4-1.1-1, #PC4.8-8.2, #PC4.14-1.2, #PC4.14-1b, #PC4.14-4.2, #PC4.14-4.5-1, #PC4.14-4.5-2, #PC4.14-4.6, #PC4.14-4.6.4, #PC4.14-5.5-1, #PC5.4-1.3-1-1, #PC5.4-1.3-2, #PC5.4-1.3-2-1 (new), #PC8.1.1. LF 31538d03f6ab, table 13b7fe003c42, pair 2786c825ab52, labels f44f17d83997, TL 6efa48e72168, NL 251b74ca0ee6. Definition check 0 conflicts. Reviewed blocks 24,315 characters. Launched 05:2x as task b6w00jmqx.

## TL (6B)-c read in full before tl-6bc r1 (9 Nov, during pc-wraps r7)
#690–#741 read line by line; arithmetic re-done. #696-0: #_{j+1}(X_D) ≤ 16.02 + 0.21σ(D) at L > 10⁶; N ≤ 176.1 + 32/M + (0.23 + 64u_𝔏/L)σ(D) ≤ 208.1 + …; 128N/L ≤ 0.03 + o(1)σ(D). #696-1: 16.1 + 0.9 + (0.23 + 8u_𝔏/L)σ(D) ≤ 17 + σ(D)/4. #698: 17 + σ/4 ≤ (21/20)σ needs σ ≥ 21.25 and 16.1 + 0.23σ ≤ (21/20)σ needs σ ≥ 19.6, both under 22; σ + 2 ≤ (21/20)σ needs σ ≥ 40. #698-1: #_k(X_D) ≤ 21.16 is an integer ≤ 21, so diam_∞(T_D) ≤ 21M. #699-2: 2^{d+1}(3/2)ℓ/M ≥ 2^{d+1}(ℓ/M + 1) + 40 as 32·46 ≥ 72; 16·46 ≥ 40; ½ℓ ≥ 46M ≥ 43M. #699-3: 2R_k − 1 ≥ 91. #716: 32 + ½ + 16 ≤ 64. #720: 21/10 ≤ u_𝔏/2, 4 ≤ u_𝔏λ_𝔏. #722: ϑ_k² = e^{−62δMR_k/512} ≥ e^{−63δMR_k/512} (#T4.53), c_r⁺ϑ_k² ≤ (ϑ_k/4)ν_r iff 4c_r⁺ϑ_k ≤ ν_r; λ_n(D) ≥ 1 − S^R − 1/32 ≥ 15/16. #724: 32.5 + 276M ≤ 64 + 1280M. #726: 2ν_r#π_k(X^{(44)}) ≤ p₀/16 (#655) gives (5/2)ν_r#π_k ≤ 5p₀/64. #727: (5/2)ν_r2^{d+2} ≤ c_F^×/2. #730: 17·21/20 + 4.2 = 22.05 ≤ 23, and 23C_Ψ′Mε^r_k² ≤ (ε^r_k/2)ν_r iff 46C_Ψ′Mε^r_k ≤ ν_r (e^{−p₀/2} = ε^r_k², #T4.53). #732: (1/2 + ε/2) + (ε/4 + ϑ/4 + 1/8) + 1/8 ≤ 3/4 + 1/32 < 1. #740: 4 − 1/8 − 1 − 1/8 − 2 = 3/4, the map's 31/8 = 4 − 1/8.
Repairs (TL 6efa48e72168 → cc2687943d10, LABELS_TWO_LOOPS ba4dce65e984): #730's condition 182C_Ψ′Mε^r_k ≤ ν_r is replaced by 46C_Ψ′Mε^r_k ≤ ν_r, the weakest form of its step, also in #286's list (no other use in TL, PC, NL, BP_TL_* or the table). Wording: "booked"/"books" → "paid" (#722), "charges to" (#738), "counted" (#841-1, #844-6); PC #PC4.14.4-4.5.4-5–4.5.4-6 "booked/book/booking" → "entered/enter/the entry in W₁'s register" (pair 66b6e1fea4dd, labels 58c7fd9ed48f; not under review in r7); BP_TL_EVAL_POINTS #166-5 "budgets" → "totals" (18bb0d681b30). The TL part specs (6ba–6cb) get the current SHAs and LF 31538d03f6ab at their launches.

## TL (6B)-d read in full before tl-6bd r1 (9 Nov)
#742–#787 read line by line. #754-1: 4/34 ≤ 1/8, 8/(34·512) = 1/2176 ≤ 1/2048, 4.2/34 ≤ 1/8; Σ_je^{−cj} ≤ 1 + 1/c. #755: the two join kinds give 2^d(2 + 34M/min) ≤ 2^{d+1}(1 + 34M/min). #758: 16M + 4M = 20M per unit of D_P. #762: c_F^×/8 ≥ 5·2^{d−1}ν_r ≥ 2^{d+1}ν_r (#727); (20/21)/1024 = 1/1075.2 ≥ 1/1076. #776: e^{−31δM(log u)²/512} ≤ u^{−2} iff δM log u ≥ 1024/31 = 33.03; S^R ≤ 2Σ_n(𝔲 + bn)^{−2} ≤ 2𝔲^{−2} + 2(b𝔲)^{−1}. #778: 12·1076² = 13893312. #876 re-derived: Σ_{m≥1}L^me^{−aL^m} ≤ 2e^{−a}/a (L^m − L^{m−1} ≥ L^m/2); Σ_{m≥1}L^{2m}e^{−aL^m} ≤ 4e^{−a}(1/a + 1/a²) ≤ 12e^{−a}/a² for a ≤ 2, and for a ≥ 2, with y_m = aL^m/2 ≥ 2 doubling, a²e^{a}Σ ≤ 4Σy_m²e^{−y_m} ≤ 4(4e^{−2} + 16e^{−4} + 64e^{−8} + …) < 3.5.
Repairs (TL → e58fbb0cd54b, LABELS_TWO_LOOPS ba4dce65e984): #759's 24MC_jnε^r_k ≤ ν_r → 21MC_jnε^r_k ≤ ν_r, exactly (21/4)MC_jnε^r_k² ≤ (ε^r_k/4)ν_r (no other use); #749 cites V4 by label, sec:extent-weights and sec:two-loops-setting (read: "fine periods LK_i, with K_i ≥ 3(n+2)", and "K_μ ≥ 3(n_i+2) for every coarse period and i = 1, 2"), in place of V4 line numbers. Table fork 05:23 edits (6fcf5c2f8424, LABELS 35126366ce75): #T12.7-24/-24-1, #T10.14, #T10.1-3-2, #T10.55-1-1, #T10.1-4, #T10.10, #T10.18-0; none is used in TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT.

## TL (6C)-a and (6C)-b read in full before tl-6ca r1 and tl-6cb r1 (9 Nov, 05:26)
#789–#872 read line by line. #795: (3/8)(ν_r/8)·6 = (9/32)ν_r, (3/64)(2R_k + 1) ≤ ν_r(R_k + 1)/8, #720's bound within 6M(σ_g − λ_𝔏Σℓ_P) + 4MΣℓ_P as 2 ≤ 6·2^{d+2}, 21/20 ≤ 6, 21/10 ≤ 3. #798: 2.28 ≤ 5/2. #799: 0.890625 + 1/32 ≤ 0.922. #806: (5/2)ν_r, c_F^× ≤ 1 give (d + 1)(#π_k(Y_i) + 1) ≤ (d + 1)(102R_k)^d. #814: 2α^{1/3} = (8α)^{1/3}. #814-4-3-1: the two conditions sum to B_Q + 15e^{−p₀/4} ≤ ν_KP. #817: (d + 1)(1.02)^d/(4κ) ≤ 1/32 iff 8(d + 1)1.02^d ≤ κ, 43.3 < 96 at d = 4. #823: e^{p₀/16}e^{−p₀/2}. #828: 2^{d+1} + ½ + 4 ≤ 2^{d+2}, 21/5 + 21/20 = 21/4. #835: (ν_r/8)(21/10) = 21/80. #842-1: e^{(1 + C_y)S^R} ≤ e^{1/32}·2 < 4. #843-1: (3/32)(1.05σ + 1) ≤ (σ + 1)/10, (3/64)·43 = 4.03. #844: ½ + 1/5 + ϑ_k/4 ≤ 1. #844-2-1: 1/0.078 ≤ 13 (C_ϑ = 13c_r⁺/(eν_r), y^s_k = C_ϑϑ_k², #T4.53), 4/3 ≤ 13. #844-4-1: 31/32 − 1/32 = 15/16. #844-5: sup_{x≥1}xe^{−ax} ≤ e^{−a}(1 + 1/a), decreasing in a, so C_att at a = ν_r/(32u_𝔏M). #844-8: (33/32)·1.5⁸ ≈ 26.4 < 5000. #845-1: 17ν_r ≤ 17/640 ≤ log 2. #855-1: 88M/(2MR_k), 352M/(4MR_k) ≤ 88/R_k per domain; 88n/R_k ≤ 22Σ_PD_P/R_k² ≤ (ν_r/80)Σ_PD_P iff R_k² ≥ 1760/ν_r; 1.05/R_k ≤ ν_r/16 iff R_k ≥ 16.8/ν_r. #849: 2 + 1/256 + 3/80 ≤ 5/2. #858: 1/3 + 1/4 + 21/80 + 1/80 + 1/32 = 0.8896 ≤ 0.89.
Repair (TL → 4b31b538b1c1): #844-8 cites #286 for y^s_k ≤ 1/32, the condition behind 1 + y^s_k ≤ 33/32 (y^s_k ≤ C_ϑϑ_k alone gives only C_ϑS^R ≤ log 2). (6C)'s "bridge" (#844-4-1) is D2.6 closure 5.5's defined chain of cubes and stays.
- Table fork (table 69145ecb37d5, LABELS 8ba4f31aeaef, hashes verified): BETA §10 rows and length splits (#T10.53-3, #T10.51-1, #T10.54-1, #T10.18-1-1). The only §10 row in my files is BC's #T10.23, identical to the r7 snapshot's.
- Table fork (table 14c0bf9c3648, LABELS 86591f7ca0e6, hashes verified): #T10.28-4-2-2 records RG II's field argument 𝐀; no file of mine cites #T10.28.
- Changed since r5, all re-read twice (19): #PC4.4-1.1, #PC4.14-1.2, #PC4.14-1b.1.1, #PC4.14-2.1, #PC4.14-2.3, #PC4.14-4, #PC4.14-4.3, #PC4.14-4.5-1, #PC4.14-4.5-2, #PC4.14-4.5-3, #PC4.14-4.5-4, #PC4.14-5.5-1, #PC4.14-5.5.0.1, #PC4.14-6.1.2-4, #PC5.4-1.2, #PC5.4-1.3-1, #PC5.4-1.3-1-1, #PC5.4-1.3-1.1, #PC5.4-2.2-0. #PC4.14-4.5-2's claim checked: the wrap-free step-(i₀ − 1) occurrences are dev clusters (#PC4.14-6.3.1), whose activity differences ≤ d^{ins}_{i₀−1} ≤ d^{ins,0}_{i₀−1} + F_{i₀−1}, covered by ρ^{LF,×}_K and x_{i₀} ≤ x̄_K (#PC4.14-6.4.1, #PC4.14-6.7).

## Queued wording repairs (9 Nov, 03:24)
The math-paper-skills banned-word list (latex-math-writing/references/banned-words.md) bans "budget", "schedule" and "collar" in every sense. Only "bridge" carries the qualifier "figurative". The entry of 03:15 above, which kept "collar", is wrong. "budget" appears 12 times in TL, once in PC and 10 times in BP_TL_EVAL_POINTS; "schedule" once each in BP_TL_EVAL_POINTS and BP_TL_GC_TRANSFORMS; "collar(s)" 8 times in TL, 7 in BP_TL_EVAL_POINTS and once in BP_TL_NSTEP_FRAME. Each will be replaced by the object it names before the TL part rounds. "bridge" in D2.6 closure 5.5's sense, the chain of π_n-cubes of (T1) counted by N_𝒢, is a defined set and stays.
Done: no "budget", "schedule" or "collar" is left in TL, PC, NL or BP_TL_* (grep, 9 Nov 05:52).

## Triage: pc-wraps-20261109-r7 (9 Nov, 05:52)
Verdict: 0 fatal, 0 serious, 6 minor. Not clean; the clean count stays 0. All six repaired in place.

| Finding | Repair | Lines |
|---|---|---|
| m1: K₁ and K₁^× are least numbers; only an upper bound on them is free of the torus period | Every condition, those of K₁(C₁), K₁(C₂), k_W^× and K_Q included, holds once it holds at the period-free majorants, so K₁^× is at most the least K for those, a period-free number. The LF session was told that #C7.4-7-5-2 has the same point | #PC4.4-1.1 |
| m2: C_pc′ = C_pce^{40c_πα_{1,k+1}} depends on the step | C^{ε̂} = e^{1+2c_W}C_pc (#T4.55, changed by the table fork at my request), by C_pc′ ≤ eC_pc (map #MD2.4.12.28, #MD2.4.12.27-1). C_pc = 483C_τmax(C_τ, C_ℓ) (#MD2.4.12.26-1), with ν_f = ν/16 + ν_r and ν_e = ν/(2C_box) (#MD2.4.12.21, #T4.44). #PC4.14-1b.4.5 cites the row instead of defining it | #PC4.14-1b.4.5, #PC4.14-1b.4.5.1 |
| m3: the factor 2 of #PC4.8-2.1 is per constituent | ε̂^{(2)}_i is at most C^{ε̂} times (ii-w)'s c-version sum with its constants at the enlarged amplitudes and the decay κ − κ_I (#PC5.4-2); the threshold is ν_r/(5184MC^{ε̂}) | #PC4.14-1.2 |
| m4: c^{nw,X} unclear (recursive or not) | c^{nw,X} is run X's step-n activities with the step's wrap groups and the groups with a carried wrap set to 0, the dev groups, their merged occurrences included, kept as run X's. That is the reading #PC4.14-6.1.1's c^{w0} and #PC4.14-4.5-2's cover use. The change c^X − c^{nw,X} is supported on those groups, so η^{d,X}_n ≤ 4C^{ε̂}Σ_{m≥k−n}t_m ≤ 8C^{ε̂}τ^{w,occ}_K with no η^d_{n−1} term. #PC4.14-4.5-2 adds d^{ins} ≤ d^{ins,0} + F (#PC4.14-6.4–#PC4.14-6.4.1) and #C7.6-6-2-1 | #PC4.14-6.3, #PC4.14-6.3.2, #PC4.14-4.5-1, #PC4.14-4.5-2 |
| m5: c^0's one-line definition omits the occurrences held at i₀ | "with the occurrences of #PC4.14-1b.1.1" | #PC4.14-1b.1 |
| m6: #NL10.5-1 does not name #NL6B.2-1 | "#NL6B.2-1 in place of #PC5.4-1.3-2-1" | #NL10.5-1 |

Re-derivation of m4. At an old step n, c^X − c^{nw,X} is supported on two kinds of group. The step's wrap groups, wrap(n) insertions of mass ≤ t_{k−n}, enter δε̂ once with C^{ε̂}. The groups with a carried wrap(j), j < n, enter with 1b.5's factor 3 (#PC4.14-1b.4.2-2). Then 4C^{ε̂}Σ_{j≤n}t_{k−j} ≤ 4C^{ε̂}Σ_{m≥m_K}t_m ≤ 8C^{ε̂}τ^{w,occ}_K, since k − n ≥ m_K. For K ≥ K_Q that is at most B^H_K ≤ D^{cw}_K ≤ ν_r/(10368M): B^H_K ≥ 16C^{ε̂}τ^{w,occ}_K, D^{cw}_K ≥ 1024B^H_K and C^{ε̂}_1 ≥ 1. The middle bracket's dev groups are run X's whole, so their two-run differences are the marks d^{ins}_n ≤ d^{ins,0}_n + d^{ins,o}_n, and the pair's (8.3) with o is linear (#PC4.14-6.4). The recursive reading would also move the carried dev insertions, a term the recursion does not have; it is not the note's. m2: C^{ε̂}·ν_r/(5184MC^{ε̂}) = ν_r/(5184M).

Rechecks, two full passes. Every changed line re-read in context. Consumers grepped:
- C^{ε̂}: every PC use is an upper bound, so the larger constant only strengthens the K_Q and (KP^{(2)}) conditions, which still hold for large K and small g. NL #NL10.4-5 ("constants of ν, L, M") holds, as ν_f and ν_e are multiples of ν.
- c^{nw}: #PC4.14-1b.7–1b.8's c^{nw} is another object (carried wraps only, at every step); its recursion is a valid upper bound and is not changed. #PC4.14-4.5-3, #PC4.14-4.6, #PC4.14-6.3.1 and #PC4.14-6.5 are consistent.
- The threshold ν_r/(10368MC^{ε̂}) is used nowhere else.
- "free of the torus period": #PC5.4-3.1 speaks of the majorant, which is correct.
#PC4.4-2's sentence ended in a comma continued by #PC4.4-2.1; it now ends with a period, and #PC4.4-2.1 opens "The young steps also lie" (wording only). Shared files were hash-checked before writing (pair 66b6e1fea4dd, NL 251b74ca0ee6).

Repaired SHAs: pair 7c09e0dc21ec, LABELS_PAIR_CAUCHY cc214e59e23f, NL bb69425f401d.
- Table fork (05:40): #T4.55 now reads C^{ε̂} := e^{1+2c_W}C_pc (table f44f990130f3, LABELS 5bc2ff823179); re-derived as above. It asked about the other C_pc′ uses (#T12.7's C_ε̂, K₀, d(𝒢), κ_pc): they belong to the Cauchy note and the map. I answered that they need e·C_pc wherever K- or g-freedom is claimed, and that the change is for their owners.
- Table fork (earlier): 086e56ef73fe, LABELS 412958ee8c08; no row of mine changed.
- LF note now b142ee965e51 (LF session).

## Pre-check: pc-wraps_a-20261109-r1 (9 Nov, 05:52)
pc-wraps r8 measured 26,364 characters of reviewed blocks with #PC4.14-1b.4.5–1b.4.5.1 and #PC4.14-6.3–6.3.2 added. It is split at §4/§5:
- part a: §4's lines and #NL10.4–#NL10.4-3;
- part b: #PC5.4–#PC5.4-3.1, #PC8.1.1 and #NL10.5–#NL10.5-1, launched after part a.
Each part needs two consecutive clean rounds, the second full; every round of either part is full.

Part a under review: #PC4.4-1–#PC4.4-2.2 (extended from #PC4.4-2, which #PC4.14-4.6.2–4.6.3 cite), #PC4.8-8.2, #PC4.14-1.2, #PC4.14-1.4, #PC4.14-1b–1b.1.1, #PC4.14-1b.4–1b.4.2-2, #PC4.14-1b.4.5–1b.4.5.1, #PC4.14-2–2.3, #PC4.14-4–4.6.4, #PC4.14-5.5-1, #PC4.14-5.5.0.1, #PC4.14-6.1.2-4, #PC4.14-6.3–6.3.2 and #NL10.4–#NL10.4-3. Reviewed blocks: 17,027 characters.

Changed since r7 (11): #PC4.4-1.1, #PC4.4-2, #PC4.4-2.1, #PC4.14-1.2, #PC4.14-1b.1, #PC4.14-1b.4.5, #PC4.14-1b.4.5.1, #PC4.14-4.5-1, #PC4.14-4.5-2, #PC4.14-6.3, #PC4.14-6.3.2 (and #NL10.5-1, for part b).

The whole part was read before launch:
- #PC4.4-2.2: P_i(X) ≥ ⌊k/2⌋ − m_K + 2 ≥ 3k/8 + 3/2, from ⌊k/2⌋ ≥ (k − 1)/2 and m_K ≤ k/8.
- #PC4.14-4.6.2: ⌊k/2⌋ − m_W + 1 ≥ 3k/8 + 1/2.
- The definition check found 0 conflicts after #PC4.14-1b.4.5 cites #T4.55.
SHAs: LF b142ee965e51, table f44f990130f3, pair 7c09e0dc21ec, labels cc214e59e23f, TL 4b31b538b1c1, NL bb69425f401d.
Launched 05:53 as task bxwzoxu7w.
- After the launch, outside part a's lines: #PC8.1–#PC8.1.2 became three sentences (wording only), and the pair note is 10120fdd4148 (LABELS_PAIR_CAUCHY 847d753ffa8a). spec_pc_wraps_b_r1 is written: #PC5.4–#PC5.4-3.1, #PC8.1–#PC8.1.2 and #NL10.5–#NL10.5-1 under review, 10,376 characters, 0 conflicts. Its pre-read re-derived the following. #PC5.4-2.2-2: 81Mσ·ν_r/(5184M) = a°/2 twice. #PC5.4-2.2-4: Cauchy with u₀^∨ ≥ 2 gives (2/u₀^∨)(A^{cr,2}_E + A^T_Eu₀^∨δε̂^∨) ≤ D^{cw}_K(c″A^{cr,2}_E + 2A^T_E). #PC5.4-3: the three sources sum to Δ^{E,cr}_K, with S ≤ e^{−a}(1 + 2/a) by #876.
- LF session (05:53): the Cauchy note is 054141083507, with #C7.4-7-5-2's K₁ ≤ K̄₁ (part a's snapshot d0ba29aae4bb already has it), #C7.8-1-3-1's C_ε̂ := e^{2c_sh+2}C_pc (another symbol than #T4.55's C^{ε̂}), and §10's contour variables. No file of mine quotes §10, Q′₁, Q̄₁ or Γ_{y,x} (grep).
- Table fork (05:58): table 6af3278b159c (hash verified), LABELS 064cb91459fe. #T12.7, #T12.7-4, #T12.7-7–7-2, #T12.7-24-1, #T12.7-27 and #T12.9 changed; none is cited in TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT (grep).

## Triage: pc-wraps_a-20261109-r1 (9 Nov, 06:24)
Verdict: 0 fatal, 1 serious, 5 minor. Not clean; part a's clean count stays 0.

| Finding | Repair |
|---|---|
| S1: c^0 undefined on the step's wrap groups (the wrap(i) productions, which have no wrap member), notably at i₀ | c^0 holds them at run A's whole at every young step. Edited #PC4.14-1.4, -1b, -1b.1, -1b.1.1 (explicit list: dev B's whole, the step's wrap groups A's whole, at i₀ the groups with a wrap member hold A's occurrences; cross groups 0), -1b.4 (Δ^w_i includes them), -1b.4.1 (changed whole with the factor 1 in the first change), -1b.4.2-1, -1b.4.4, -4, -4.7.2, -6.1.1 (c^{w0}: dev B's whole, all other groups A's whole), -6.2, and part b's #PC5.4-1.2, -1.2-1, -1.3, -1.3-2.1, -2.2 |
| M1: cube positions in (KP^{(2)}) need the box reduction | #PC4.14-1.2 split into -1.2 and -1.2-1: the box spare fits, since 3/8 + 1/L + 1/4 ≤ 1 (#MD2.4.12.29), and the cube sums are at most C^□ := Σ_{R≥0}8M(2R + 3)e^{−(ν_e/4)R} times the traversal sup (#MD2.4.12.30); the threshold is ν_r/(5184MC^{ε̂}C^□) |
| M2: "with every wrap removed" in #PC4.14-6.3 | phrase deleted; the explicit clause stays |
| M3: 8 can be 4 in #PC4.14-6.3.2 | the chain shows ≤ 4C^{ε̂}τ^{w,×}_K ≤ 8C^{ε̂}τ^{w,occ}_K |
| M4: N_C enters through §6A's counts | #NL10.4-2: "N_C enters them only through the constants of §6A–§7 in their bounds"; #NL10.4-3 names #NL6A.8's per-position counts; #NL10.4-5 lists C^□, names c_W with #NL6A.9's share coefficients and L ≥ L₀^{(N)}, and calls B^H_K #PC4.14-5.5.0.1's with these constants |
| M5: #PC4.14-1's threshold | "once ε̂_i ≤ ν_r/(1296M), the condition of #MD2.4.12.38-2" |

Re-derivations:
- S1. At a young step the groups are dev groups, groups with a wrap member, the step's wrap groups and cross groups (activity 0, #PC4.14.3); a D_g with a wrap member is wrap(k) (TL #842), so the step's wrap groups are the wrap(i) productions. δc on them is the full birth difference. It lies in d^w_i, since the step-i births are sources of e^{cw}_i's recursion (#PC4.14-5.4, fresh, carried and, at i₀, outer parts #PC4.14-5.5-1). Their weight is within C^{ε̂} (#PC4.14-1b.4.5), so the first change is at most 3C^{ε̂}(carried) + C^{ε̂}(step's wrap groups) ≤ 3C^{ε̂}Δ^w_i, and Δ^w_i ≤ 2τ^{w,×}_K + d^w_i ≤ 2τ^{w,×}_K + e^{cw}_i, as #PC4.14-5.4.1 already uses. No constant changes.
- At the old steps c^0 is unchanged: run A's carried wraps, run B's fresh constituents and occurrences at the previous step's c^0, so #PC4.14-1b.7's c^{nw} is still the same for c^B and c^0.
- #PC4.14-6.2. c^{w0} = c^A off the dev groups, so c^{w0} − c^A changes only dev groups. c^0 and c^{w0} agree on the dev groups and the step's wrap groups, and on the groups with a wrap member they differ by the fresh part (fresh constituents, and occurrences from c^A_{i−1} to c^0_{i−1}), which is at most e^{cw}_i (#PC4.14-5.5.0.2). So δε̂^d_i ≤ δε̂_i + C^{ε̂}e^{cw}_i ≤ C^{ε̂}_1H^{cw}_i, as before.
- #PC4.14-4.7.2. δε̂ now takes the step's wrap groups' fresh differences. These are birth differences bounded by e^{cw}_i's sources (8ρ^{LF,×}_K, r̄_K, e^{−C_Pk/4}, τ's, x_i), which hold no c̄^W_K. The other activities' fresh differences stay in Q^0 − Q^A, and LF #5.42's comparison is unchanged, since holding activities at run A's lowers their relative differences.
- §5. The T-part's ς-end holds the same data, so #PC5.4-2.2's identification with c^0 stands. #PC5.4-1.3-2.1's agreement covers the held activities through (L×) in run A.
- M1. ε̂'s weight is C_pc′e^{sh+b+(ν_r/4)σ}. With e^{(ν_e/4)ext} the exponent is at most (3/4)ν_rσ + (5/8 + 1/L)ν_e·ext + 2c_sh ≤ ν_rσ + ν_e·ext + 2c_sh for L ≥ 8/3. Also C^□ ≥ 24M ≥ 1, so the traversal positions are covered by the same factor.
- M4. TL #561–#564: the cube count Σ_i(8|H_i|/M + 80) and the bond count are per loop, so c_sh^×'s constants grow with N_C, as #NL6A.9's share coefficients do. C^□ depends on M and ν_e only.
- #PC4.4-1.2: "For K < K₁^× the bound 2B^×_W of #PC2.4-6 is used" (#PC2.4-6 checked).
- Grep: "all else run B's", "every wrap in the occurrences" and "every wrap removed" have no other live use. "c^0" in the table: #T12.3-3 restates it, and the table fork is asked for a pointer row instead. C^□ is a new symbol, with no clash in the table, the notes or balaban_proofs/ (the map's C_□ is Bałaban's operator); a pointer row is asked for.
- Lengths: #PC4.14-4 is ≤ 600 after shortening (labels_pair_cauchy reported 601 first). The longest changed line is #PC4.14-6.3.2, at 570.
- Not cited by my files (grep): #T10.28-3-4, #T1.4, #T10.21 (table 4f338b69054c), #T12.7-23, #T12.7-23-1, #T6.5-2 (tables 541c27303c76, e87be282550b).

Repaired SHAs: pair fad8a918b02e, LABELS_PAIR_CAUCHY e70a8c256d9a, NL f5efec3d2283; table e87be282550b.
- Table fork (06:26): table a59d81743856 (hash verified), LABELS 160897034a78. #T12.3-3 now cites c^0 by pointer to #PC4.14-1b.1–#PC4.14-1b.1.1, with no ":=" on c^0. It carries C^□ as a pointer to #PC4.14-1.2-1 and separates it from the C_□ of #T12.6, #T12.6-7-1, #T12.9 and #T12.24-1-0. Part b's definition check gives 0 conflicts at this table.
- Table fork (06:34): table fa191df06f65 and LF bbaa009a3313 (both hashes verified), LABELS 88555cb681d5. The changes are #T12.9's w_Z, #T4.35's (1 + d²)C_w(ε₀) clause and an LF relabel. No file of mine cites #T12.9 or #T4.35 (grep). spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork: table 197ee9e2d0ff and LF 56d172c27cf2 (both hashes verified), LABELS 0b3bbed47643. The LF's C_ζ and c_w (#T12.9, #T12.12) now use c_ζ. That c_w := 4(d − 1)(1 + c_ζ)C₀^{ms} is the LF's, which #T12.12 separates from #T4.47's c_w, the one TL #568 and #893 use, so nothing of mine changes. spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork (06:49): table ad8ae39e2f9c (hash verified), LABELS 2990d8734bd6, LF unchanged at 56d172c27cf2. BETA's rows changed: #T10.21 is split, adding #T10.21-2, and #T10.28-3-1 is restated. No file of mine cites #T10.21, #T10.28-3-1 or C̃^{(2)} (grep).
- Table fork (06:50): table c9661181fd5a (hash verified), LABELS f7b9cbcc004f. Only #T10.21-2's used-in column and sources changed; I don't cite that row.
- Table fork (07:22): table 75715b244ad6 and Cauchy a0b36ebcf1d0 (both hashes verified), LABELS ff427ec1b000, LF unchanged, for the Cauchy 14b r2 repairs. Changes: δ₂ = δ₁′ in #T3.27, #T12.7-23 and #T12.15; C_𝐆, c_{GM}, c_e and x_λ updated; new rows #T12.7-24-2 and #T12.7-24-3. Checks:
  - My only citation of these rows is BP_LFR2_REPLACEMENT #160.0-1, which cites #T3.27 for ε_k, and ε_k is unchanged.
  - None of the changed symbols appears in TL, PC, NL, BP_TL_*, BC or BP_LFR2_REPLACEMENT (grep).
  - Against part a r1's snapshot, the Cauchy note's changed lines are all in §10 and CK.1. No file of mine cites #C10.* or #CK.*, and none of the 71 Cauchy tags that PC and NL cite changed.
- Table fork (07:28): table 2396f07aafeb (hash verified), LABELS 62079add07c0, after BETA's BH10b-7. #T10.28-4-2-1-1 now marks B′ inferred, and #T10.28-4-2-2's RG1 p.276 pins are corrected. My p.276 pins (BP_TL_GC_TRANSFORMS #6.12.2–#6.12.3, BP_TL_EVAL_POINTS #17-1) are to CRE p.276, a different paper, and no file of mine cites #T10.28-4 (grep).
- Table fork (07:58): table 0d6adc9e81d4 and LF 6ac728004094 (both hashes verified), LABELS 9faef7334bc0. #T11.19's REG (1.14) pin is now p.78 l.14–18 and #T11.19-2's p.77 l.17–18; #T12.12(a) adds the c_av clash. I don't use c_av. BC #BC.3-1 cites #T11.19, so I re-checked every REG p.76–p.82 pin in my files against REG\parts (corrected line = raw line − 1, the pagemark line dropped):
  - BC #BC.3-1 had p.078 l.13–17 for (1.14)'s invariance, which is raw 15–19, so corrected l.14–18. Fixed (pin only, bookkeeping). BC is now ea5707f29e5b, and bc38a r21 sees it.
  - The others are right: BC's p.076 l.31–47, l.40 and l.41–42; p.077 l.32–40, l.48 and l.48–52; p.078 l.44–48 and l.50–54; p.079 l.2–15 and l.15; p.081 l.33–35; p.082 l.4–10. BP_LFR2_REPLACEMENT's p.78 l.14–37 and p.079 l.17–28. BP_TL_EVAL_POINTS's p.78 l.14, p.79 l.4–9 and l.15. BP_TL_MIXED_TERM's p.79 l.4–8 and l.12. BP_TL_NSTEP_FRAME's p.79 l.4.
  - spec_pc_wraps_b_r1's lf_sha is updated to 6ac728004094.
- Table fork (08:09): table 0b9312c28f58 (hash verified), LABELS 0d0957612a48, LF unchanged, after BETA's BH11b-5. Rows touched: new #T10.28-3-1-3-2, plus #T1.4, #T10.28-3-1-2-1 and #T10.28-4-3. No file of mine cites #T10.28*, #T1.4 or K_{F₃} (grep).
- Table fork (08:28): table a9ff90c0cf7f (hash verified), LABELS 40cd822d99e0. Only #T10.28-3-1-3-2 changed (wording); I don't cite it.
- Table fork (08:43): table b9cb1fe93596 (hash verified), LABELS 39857d2caa24. #T12.24-1-2-1 changed and #T12.22 was split into #T12.22 and #T12.22-0-1. No file of mine cites #T12.22* or #T12.24* (grep).
- Table fork (08:50): table 8b8f7c1733bc (hash verified), LABELS 6dd1919a39c2, after BETA's BH13-1. #T10.36-4 and #T10.36-4-3 changed. No file of mine cites #T10.36* or uses σ_H (grep).
- Table fork (08:52): table 3f73b58833dd (hash verified), LABELS c7ac77a7f926. #T12.12(a) adds the σ_H clash. I don't use σ_H.
- Table fork (09:21): table a63138631eb6 (hash verified), LABELS 33ee63b855ee, after BETA's BH14-1. #T10.36-4 and #T10.36-4-3 changed; I don't cite them (grep at 08:50).
- Table fork (09:26): table b5ec74b360de (hash verified), LABELS 3b017cd21455. Only #T12.7-27 changed; I don't cite it (grep at 05:58).
- Table fork (09:28): table a48e60eaa64a (hash verified), LABELS d0901ef4bb50. Only #T12.28-3-1 changed; no file of mine cites #T12.28* (grep).
- Table fork (09:31): table cca252355a80 and LF a07ed7efe24d (both hashes verified), LABELS 3128e67a0398. New row #T11.20-2, PBG's penalty coefficients a_j. No file of mine cites #T11.20* or uses PBG's a_j (grep). spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork (09:35): table db331ee55977 and LF 73435a4a8e2a (both hashes verified), LABELS 54e113fa9642. Only #T11.20-2 changed; I don't cite it. spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork (09:37): table 0e8cb42f87e0 (hash verified), LABELS 22c9a3403920. CRE (2.6)'s β′ and β₀ moved from #T10.1-3 to #T10.1-3-0, and #T6.21 is reworded. No file of mine cites #T10.1-3 or #T6.21 (grep), so no pointer needs moving.
- Table fork (09:39): table d1f8573185e2 (hash verified), LABELS f16b9103c444. Only #T12.28-3-1 changed (wording); I don't cite it (grep at 09:28).
- Table fork (09:49): table 48ed6504f348 and LF 8d84c228e098 (both hashes verified), LABELS 44bfa18fd4a2. #T12.9's c_v and #T12.7-24-3 changed, the latter adding c₁₂₄ and the Cauchy-local c_D := 9(2d + 1)(2d + 2)k_G². My c_D's are other objects, each defined in place: TL #253's weight ⅓ or ½, and BP_TL_EVAL_POINTS #197's sup of abs(∂_V(hD̃(B)))/abs(B)². I don't use c_v or c₁₂₄ or cite #T12.7-24*. spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork (09:54): table 862a80d8ea69 and Cauchy d4c3ddcc30ef (both hashes verified), LABELS 4313770ebbb2. #T12.7-31's C(ε₀, γ_H) now matches #C10.4.123. No file of mine cites #T12.7-31 or uses γ_H or C_δΔ (grep). Against part a r1's snapshot, the Cauchy note's changes outside §10 and CK are #C5.22-3, #C9.4-1 and #C9.8.6-3, and no file of mine cites #C5.22*, #C9.4* or #C9.8* (grep).
- Table fork (09:55): table caa7b14319a3 (hash verified), LABELS 89a09b0bb330. BETA's #T10.12 and #T10.41 changed. No file of mine cites them or uses c_𝒞 (grep).
- Table fork (09:57): table eb8a5723c2b2 and LF 029a1d03a304 (both hashes verified), LABELS a913f25dfc3f. C_{Q*} is now stated once, at #T3.13, and #T4.14's C_ℒ′ is marked as W-δ's. No file of mine uses C_{Q*} or C_ℒ′, or cites #T3.13, #T12.6-5 or #T4.14 (grep). spec_pc_wraps_b_r1's lf_sha is updated.
- Table fork (09:59): table 1e464ebebe51 and Cauchy b3ae2ca96d3a (both hashes verified), LABELS 3076a41eaa7c. #T12.7-28 names T_Q := Q₁Q₁*. No file of mine cites #T12.7-28 or uses T_Q (grep). The Cauchy note's changes outside §10 and CK are still only #C5.22-3, #C9.4-1 and #C9.8.6-3, none of which I cite.
- Table fork (10:13): table 611d15a06e81 and Cauchy 4c3614eed5e5 (both hashes verified), LABELS 8c04ad0e29d7. #T12.7-24-2 changed, and the new #T12.7-24-4 holds Cauchy's BCH constants c_B and r_B. My r_B is VAR's radius C₁ε₁/2: BP_TL_EVAL_POINTS #94-1 with C₁^{VAR}, and BC #BC.5-1-0 with C₁ = L³. #T12.7-24-4 already separates it from Cauchy's r_B (#T4.30, #T12.27-1-3). I don't use c_B or cite #T12.7-24* (grep). The Cauchy note's changes outside §10 and CK are unchanged (#C5.22-3, #C9.4-1, #C9.8.6-3).
- Table fork (10:15): table 40e20f5e4530 and Cauchy 1f73875e3b26 (both hashes verified), LABELS 3a2b74eff243. The BCH radius is renamed r_{BCH}, which removes the r_B clash with my VAR radius. No change for me. The Cauchy note's changes outside §10 and CK are the same three.
- Table fork (10:24): table 1e252f854c47 (hash verified), LABELS 7de12f87e5de, after BETA's BXa1. #T10.50, #T12.24*, and #T10.56-1 changed. No file of mine cites them or uses δ₁′, δ_cx or N_σ (grep).
- Table fork (10:33): table 0fc5618dd0d4 and Cauchy cae2edf1313c (both hashes verified), LABELS b5585ab6e0f2. #T10.43's usage column now names Cauchy #C10.1.4-0-1 as a user of "L odd"; the row's content is unchanged. No file of mine cites #T10.43 (grep). BP_TL_MIXED_TERM #5.10.6-4 uses odd L for its own slab argument and needs no change. The Cauchy note's changes outside §10 and CK are the same three.
- To LF (yang mills 4 handover (4)), 9 Nov: three stale status lines, none changing a bound. (1) Continuum #NP.2 and #NP.2-4 call TL #86, #88.1, #157 and #160 OPEN; they are derived in BP_TL_EVAL_POINTS and BP_LFR2_REPLACEMENT. (2) Map #MOMST.4-2 points to an SW S1 OPEN at #MOMGD.5, which now reads "Derived, not reviewed". (3) D2.7 items 4, 6 and 9 carry "not derived" headings although the header puts the observable part in item 15. Also TL #302: the continuum note's single-loop E_const bound lacks D2.7 15.4(ii)'s 𝐑-step remainders, which #C7.6 and the pair and N-loop bounds include. The table fork's old pipe was stale (ENOINBOX), so the message went to the LF session by name.
- From LF, 9 Nov: (1) items 4, 6 and 9 of D2.7 are cited by items 5, 7, 8, 10, 11, 15 and the header, so removing them means re-cutting items 4–11 against item 15; LF is putting that to the user. (2) The step map is on LF's never-edit list, so #MOMST.4-2 needs the map's owner. (3) Continuum #NP.2 and the C^R_E term (TL #302): LF's ownership list doesn't name the continuum note, so LF is confirming with the user; its proposed repair adds C^R_E as in #C7.6-6-1 and marks #86, #88.1, #157 and #160 "derived, not reviewed" with their BP pointers.
- From the fork yang mills 4 handover (2) ⑂, 9 Nov: step map C_pc′ := eC_pc, free of the step (#MD2.4.12.28, new #MD2.4.12.28-0); O6 §§3 and 7 cite #T11.12-2; #T12.17 updated. Hashes verified: table 255b386434fb, LABELS 07bece4ac73b, LF 029a1d03a304, map 7e6f1e0e4136, O6 0786e61bbd77. My uses of C_pc′ are re-pointed with no bound changed. In #PC4.14-1b.4.5, s(W′) of #MD2.4.12.38 contains log C_pc′, so e^{s+(ν_r/16)σ} = eC_pc·e^{sh+b+(ν_r/4)σ}, and C^{ε̂} = e^{1+2c_W}C_pc (#T4.55) holds with equality in place of "≤ eC_pc". In #PC5.4-2.2-1, C_pc′ = eC_pc ≥ C_pc ≥ 1. Both now cite #MD2.4.12.28-0. TL #585 names C_pc only, and BP_TL_EVAL_POINTS cites O6 §§4–5 but not §3, §7 or #T11.12-2 (grep). PC is 5a39b76511c3 (LABELS_PAIR_CAUCHY e70a8c256d9a, 347 tags). spec_pc_wraps_b_r1 is re-pinned and --check gives 0 conflicts; #PC5.4-2.2-1 lies in its reviewed range.
- From LF, 9 Nov: TL #302 is applied in the continuum note (aac188148373). B_E := C_Σ𝔞̄ + 2ℓ_CC^R_ES_E (#ND.5.3), with the 𝐑-parts in #ND.5.3-0 from D2.7 15.4(ii) via #C7.6-3; downstream bounds use B_E; #NP.2 now reads "derived, not reviewed" with BP pointers. LF #3.99-1 is at b510202f38c5 and Cauchy #C1.2-4 at edff26c92ecd. All hashes verified.
  - Re-derived #ND.5.3-0: at j = K′ − m, #C7.6-3 gives ≤ 2C^R_Eℓ_CL^{m+1}e^{−(c^R_E/L)L^{m+1}}, and since a_E ≤ c^R_E/L the sum is ≤ 2ℓ_CC^R_ES_E (#T4.37–#T4.38). Correct.
  - TL #302 deleted, as the omission it recorded is repaired; no file or table row cites it. TL #884–#890 are kept: C^{R°}_E carries e^{−p₀(ḡ_R)/2}, which #904's smallness needs and B_E's 2ℓ_CC^R_ES_E drops (it uses e^{−p₀/2} ≤ 1), so the two bounds are not one fact. #890 is unchanged.
  - My other uses are unaffected: TL #909/#915 use the continuum note's identity (2); TL #920 uses LF #3.99-1 only for B_LF with the soft tests, unchanged; PC #PC2.2's "as #ND.8.1 does for one loop" (1 − w_{ℓ₀} → 1) is unchanged.
  - TL 6520c46031a6 (LABELS_TWO_LOOPS d0d4571110e6, 1396 tags). spec_pc_wraps_b_r1 re-pinned (TL 6520c46031a6, LF b510202f38c5); --check gives 0 conflicts.
- From the fork yang mills 4 handover (2) ⑂, 9 Nov: #T4.37 now gives abs(E_const) ≤ B_E (continuum #ND.5.3–#ND.5.3-0). Table 6f9ed6c5934e and LABELS 4c957104ecca verified; LF, Cauchy and continuum as above. No file of mine cites #T4.37 or uses C^E_Σ or S_E (grep). The spec pins the LF, not the table, so nothing changes.
- From the fork, 9 Nov: #T4.38's ΔE_K cap is now 2B_E, as at Cauchy #C7.6-8. Table d81eed304829, LABELS 6317ee79c65f and Cauchy 648f51a2e090 verified; LF still b510202f38c5. My only use is PC #PC5.1-1, which takes #C7.6-8's ΔE_K per loop. #PC5.5's ΔE^×_K = min(ΔE^{(1)}_K + ΔE^{(2)}_K + 2τ^{E,cr}_K + Δ^{E,cr}_K, 2E*) uses the per-loop quantities inside the sum and caps by the pair's own 2E* (#891), so the per-loop cap never enters. Summability of ΔE^{(i)}_K is unchanged. No edit needed.
- From LF, 9 Nov: the D2.7 re-cut (user-approved) deletes items 4, 6, 8, 9 and 11 (D2.7 be25e365aea7, verified). My #7 block and the (R-eval) line are untouched. My only citations of deleted items are TL #637, #651 and #783 (grep over TL, PC, NL, BP_TL_*, BC and LFR2). Re-derived from LFR II p.388 l.28–30 ((1.93)), p.389 l.20–28 and l.43 ((1.95), (1.97)), p.391 l.11–19 ((1.103)) and p.376 l.26–33 ((1.67)):
  - (1.95) gives e^{−(1+β)κd_{k,∪Y_i}(X′)} for the polymers of (1.72)'s curly bracket ((1.90)), which is D2.7 15.3's gas. β → β/4 (p.391 l.17) is for (1.103)'s square bracket only. TL's old e^{−(1+β/4)κ…} citing item 6(b) is replaced by (1.95). The decay is larger, and TL's own (6C) line #791-area (l.640) already reads (1+β).
  - TL #637 is rewritten, with the new #637-0. #637 now defines P∖fixed := X′∖∪_iY_i, the fixed domains being the second-class Y_i: the symbol was used in #637, #814-4-2-3 and #814-4-2-4 and in D2.7 15.4 without a definition. With (1.67), d_{k,∪Y_i}(X′_r) = d_k(X′_r) since X′_r meets no Y_i. #637-0 keeps the size step, and the rest e^{−βκd_k} contains the two factors e^{−(β/8)κd_k} that #637-1 ("one", "the other") uses; (β/8)κ ≥ 3·2^{d−2} still holds by p.389 l.12. #816 now points to #637-0.
  - TL #651: c₁ = e^{−p₀(g_k)} is (1.95)'s factor extracted before the sum (p.389 l.27–28), as in D2.7 15.3. This matches #649's e^{−(3/2)p₀} = e^{−p₀}·e^{−p₀/2}, the e^{−p₀/2} going to (1.96).
  - TL #783: "with its *Corrections* (a)/(b)" removed; D2.7 item 5(a) reads ‖𝒯_X[w_X]‖ ≤ sup‖w_X‖ ≤ e^{2ΣA}, and item 5(b) reads e^{3 sup|σ|} ≤ e³ (p.379 l.31–32).
  - LF's question (item 2's last clause, the D26 bounds of the unchanged components after R): TL does not derive it. #7 covers the 𝐑-step's evaluation points Φ(𝐔), 𝐔 ∈ 𝒟^{ev}_k, of the class operations (#222, #229, #6.13) and of the second-class 𝐓′_k(Y_i) (#230, #785). For the insertions that R leaves unchanged TL inherits D2.7 15.8 (#299). So the item is open on my side too.
  - TL 8f524bd266db, LABELS_TWO_LOOPS a26cb65d6c9e (1397 tags); #637 is 307 characters and #637-0 362. spec_pc_wraps_b_r1 re-pinned, and --check gives 0 conflicts. The tl-6 specs get fresh SHAs at launch, as planned.
- From LF, 9 Nov: D2.7 ff4f8e28fe40 (verified) cites #637 for P∖fixed and #637-0 for the size step, and item 2's last clause stays open. One notational point was sent back: D2.7 15.4 writes "P∖fixed := P∖∪_iY_i" where TL #637 has X′∖∪_iY_i, X′ = dom P, the localisation domain. D2.7 elsewhere writes dom P, so "dom P∖∪_iY_i" would match.
- From LF, 9 Nov: D2.7 1fcd9c00ecf8 (verified) reads "P∖fixed := dom P∖∪_iY_i (two-loops #637)". Closed.
- From the table fork, 9 Nov 12:2x: TL #884 misquoted D2.7 15.4(ii): MR_k missing, /2 for /4, rate c in place of c/(MR_k), ι_{T,k} not the map's. Checked against D2.7 l.136 and map #MD2.0.5.40; all four confirmed. Repaired, 9 Nov 12:34:
  - #884 now quotes 15.4(ii) as printed, with #T4.37's C^R_E, c^R_E, and converts the cube units explicitly. #885: N_min^{(k)} = N_sL^{K′−k} ≥ 2s_k (#334, #290), and the background closure §3.2 (*The 𝐑-parts*) bound applies with K′, ℓ_i. Re-derived line by line: ι_{T,k} ≥ s_k/2 − ρ_dep; bracket ≤ e^{cρ_dep}(2s+1)e^{−2y}; MR_k ≤ R̂_{K′}m̂^{β₀} and p₀(g_k) ≥ p₀(g_{K′})/(1+β₀) by CRE (2.5), (2.7) with n = K′; sum lemma #876 at base L^{1/2} (its proof holds for real base ≥ 2).
  - #886–#889: C^{R°}_E := 2C^R_1R̂_{K′}²(2 + 24R̂_{K′}/c^R_E)e^{−p₀(g_{K′})/5} ≤ 2e^{−p₀((1+β₀)g_K)/6}, free of ℓ_i; the polylog absorbed by e^{p₀/30}, p₀ ≥ 5r ≥ 10 (CRE p.245 l.34, p.246 l.14). #904 now cites #889; #919 lists g_{K′}.
  - NL #NL7.1-2 (N_C copies) and #NL7.2 repaired to match.
  - TL 808457f540ee, LABELS_TWO_LOOPS d78ca7718b9d (1397 tags), NL 477178f4c07b. spec_pc_wraps_b_r1 re-pinned; --check 0 conflicts. Part b reviews none of the changed lines (#NL10.5-1 uses E* by name).
  - Consumers owned by LF: table #T4.52 (C^{R°}_E's formula) and #T12.2-15 (E*, unchanged in form). Messages sent to LF and the fork.
- From LF, 9 Nov: D2.7 e88981b21801 closes item 2's last clause with #39-2, #60, #72–#76, #130, #222-1, #222.1, #222-2, #229, and #5. Checked against BP_TL_EVAL_POINTS 18bb0d681b30. Supported, with two precisions sent back. (2) The value is D(Φ(P(𝐔))), equal to D(Φ(𝐔)) on 𝓜^c (#39-3, #130); off 𝓜^c the bound goes through P (#76). (3) #60's bounds hold at family points; at part (b)'s pairs #6.8's conjugation factor enters once (#130.15.1). The earlier remark on #7 is withdrawn: #7 bounds the class's members, and (3) supplies D26 5.1's conclusion.
- From LF, 9 Nov: D2.7 55d8246f93a0 applies both precisions; text verified. The table is the fork's to edit, so #T4.52's new C^{R°}_E entry went to the fork; #T12.2-15 is unchanged. LF's per-step Cauchy #C7.6-3 (Cauchy 785c3a36fed5, continuum 3ded0274387d) touches nothing in TL, PC or NL (no uses of B_E, A^R_E, b^R_E, #C7.6-1–#C7.6-5).
- From the fork, 9 Nov 12:39: table 3f044f23ff9e (LABELS 65f0b227aea3, LF f9aee603cdc7); #T4.52's C^{R°}_E entry verified verbatim against #889. spec_pc_wraps_b_r1's lf_sha re-pinned to f9aee603cdc7; --check 0 conflicts. The background closure §3.2, which #885 rests on, is under the fork's round it1-bg-20261109-r4; a change there means re-deriving #885–#889.
- User, 9 Nov: the LF session owns the step map. Sent to LF with the stale #MOMST.4-2 parenthesis (S1 OPEN at #MOMGD.5, which now reads "Derived, not reviewed"; map 7e6f1e0e4136).
- From LF, 9 Nov: LF holds the #MOMST.4-2 edit until the user confirms the ownership in LF's own session (a peer's report is not its user's instruction), and asks that this session not edit the line. Agreed; no edit here. SW closure l.112 verified: "reviewed; not closed as a whole. (6c) is derived in the covariance note, which is not reviewed … for re-review". LF's proposed parenthesis matches it.
- From LF, 9 Nov: the user confirmed the ownership in LF's session; map 55e28f01e487, #MOMST.4-2 verified verbatim. Closed. Part b --check still 0 conflicts.
- From the fork, 9 Nov: background closure 96f8f4c2ab91 after r4; §3.2 *The 𝐑-parts* (l.72–77) re-read: the fine-chain bound, C^R_1, R̂_K and r^R_K unchanged; #885 cites it by section and uses only the fine chain, so (iii-d) does not enter. Its l.75 notes 15.4(ii)'s p₀(g) may lack A₀ (table #T10.2-1); #887 now reads "a positive constant times (log g_{K′}^{−2})^{p₀} (A₀ in CRE (2.4), 1 in LFR II, table #T10.2-1)", which the absorption and the monotonicity need, nothing more. TL 4c2d342a9417, LABELS_TWO_LOOPS d78ca7718b9d; spec re-pinned; --check 0 conflicts.
- From the fork, 9 Nov: background note 44f58683dac5 derives D2.7 item 15 for the coarse chain's 𝐑-steps ((iii-d)), citing TL #48, #7 (#222-2, #130–#136), #222. No edit of TL asked. Reply sent: #222-2's landing holds for 𝐔 ∈ 𝒟^{ev}_k, defined by the next T-step's points (#222-1, #222.1, data in 𝒟^λ_{k+1}, #54) with #72's λ from the fine chain's constants; the coarse use needs its T-step's points in that set, or an inclusion stated. Will notify the fork if #7, #48 or #222 move.
- From the fork, 9 Nov: agreed; the inclusion goes into (iii-d) after r6. Its argument: the step map's operations are observable-free (bg §1.1), the coarse slots are evaluated at D2.1(4)'s deformed background as the fine chain's (§4.1), and 𝔖_k's slots are integrand insertions that change neither 𝐇 nor the data. That gives the coarse T-step's points in 𝒟^{ev}_k, so #72's λ serves unchanged. Consistent with #222-1 and #222.1, which define 𝒟^{ev}_k by the T-step's points and data, not by the observable. Closed on this side.
- From LF, 9 Nov (map 75fc93c17638, D2.7 4bd083b24532): TL #288's κ_s row is #MD2.4.12.48; PF's (T′) is #MD2.3.5.2; #MOMGD.30 is valid; the map's transport constant is c_π′ (#MD2.1.4.27) in D2.7's (R-eval) line, the complex covariance note, and D2.6 §4.4. Re-derived against the map; applied 9 Nov 16:07 with the repairs found on the way (TL #288's κ_D′ claim, PF's traversal index, EP #171's norm), logged in the self-review file. TL 796e51462f50, NL a5e53646451c, PF 1faadf53d63c, EP fb8540716113, GC 21b5c100bdcf, D2.7 0d941483552b, LFR2 78197ab6aeb9, LABELS_TWO_LOOPS 4a4860b587a0 (1399 tags).
- To LF, 9 Nov 16:15: the above, plus three points in LF's files. D2.6 l.79 (§4.2), l.81 (§4.4), l.96 (§5.4) and l.160 (§8) apply c_π to phases sized in CRE's |·| (exp(c_πη|𝐇(b)|), 20c_πM‖a′‖_∞ ≤ 1, c_πc_CM·O(1)·4B₀e^{16κ_s}ε_H ≤ 1, e^{c_π|phase(b)|}, e^{c_πℓα_{1,k+1}}, 4c_πMα_{1,k+1} ≤ 1); each needs c_π′. Table #T12.13-1 and #T12.2-8 state the map's bound with c_π, and #T12.13-1's "equals it by homogeneity" needs abs to be the operator norm. D2.7 15.8-1(6-3) cites #815.2 for Σ_cy_c ≤ m^w_Ψ, which is #815.2-1. LFR2's 3M₀ and its consumption of LF #4.9-2, #4.48.1-1 reported; #T4.30 and #T12.18 still hold.
- From the table fork, 9 Nov 18:27: #T4.32, #T4.48, #T4.50 and #T3.34-2 are in (table e0ad601d0f13, LABELS_LF_AND_TABLE e3e7388dfb7f); the C_d row cites EP #96. No two-loops change asked.
- To the table fork, 9 Nov 18:35: four stale row pointers after the EP repairs. #T4.30: C_Q is defined at EP #41-1; C⁰_{rsp}, C_{rsp} at #42-2. #T12.2-3: P at #39; U_0(𝐔) := U_0^{(AL)}(𝐔) at #39-0 (LFR II p.375 l.9, p.366 l.21–25); T := C_Qα_{1,k}/abs(B̃′) at #41.2, with T ≥ 2 from #92; the extension at #127-1. #T11.27 and #T11.32: Bałaban's smallest Y₁ (p.373 l.15–16) need not be unique; EP #39-5-1 fixes it inside D′, and the strip facts are #39-5-2.
- To the table fork, 9 Nov 18:41: EP 351757f13e23, MX e1beed4a5f1e, LABELS_TWO_LOOPS 53ec429da93c (1420 tags). D′'s faces are those in which a cube of X outside a component touches a cube of it (#39-5-1), which #39-5-2's argument needs; #39-5-1-1 and #130-3-1 are splits; the P_Ω entry stays at #130-3.
- From LF, 9 Nov 19:05: D2.7 15.5(ii)(α)/(α′)'s domain count is invalid. RG II (1.9)–(1.11) pay e^{−(κ₁−1)} per s-cube only, so the cubes kept at s = 1 (those meeting Λ, and (α′)'s Mt_k-collar) pay nothing, and s-clusters hanging off an exempt region's boundary are unpaid. LF repairs it in place by the bijection S ↔ (S_c, D), the contracted tree length ℓ_c between exempt regions, and τ_i ≤ e^{c_π′λ_wα_{1,k}} from EP #169–#171. #613's C_{α,k}, e^{δ}, the rate 63/64 and #T4.53's c_r⁺ change; LF asks that they be held until it sends the new constants with the D2.7 SHA. Held; re-derived when the text arrives.
- To LF, 9 Nov 19:06: (α′)'s "Y₁ the domain of Dep(D)" should be Bałaban's Y₁ for D: Y₁ contains the components of Z meeting X (p.373 l.15–16), and p.376 l.10–13's factor pays only the first attachment, so the decay is along trees from Y₁(D), and the target's exempt region in ℓ_c should be Y₁(D) with its components. Derivation sent: X^𝐃_D (the cubes meeting Dep(D) and the cubes around their lower-dimensional contact faces, RG1 p.257 l.7–10); Y₁(D) ⊆ N_{3M}(Dep(D)) ∪ the components meeting X^𝐃_D (EP #39-5-1); those components are in h(D) (TL #633) or are (6C)'s second case (TL #803–#806); d_∞(K, Y₁(D)) ≥ MR_k for K ∈ 𝒦 (d_∞(K, Dep(D)) > 2MR_k; components are disjoint closed unions of MR_k-cubes, LFR I p.177 l.41, CRE p.256 l.21–22); root count 3^d(1 + 103^d)c_rσ(D) (LFR I p.177 l.26). The same holds for bonds' Y₁(i) in (α). TL #613-2-1–#613-7, #617, #629 and EP #39's parenthesis are held until LF's constants arrive.
- To the table fork, 9 Nov 19:18: EP 1608d8f8e6f0, GC bafc6ad815f6, LABELS_TWO_LOOPS 608ab0c24272. #T4.48: EP #96's C_d was #41-1's C_Q under a clashing name; K := O(C_QS_L), dependence "K: C_Q (#41-1)". #96's fine phase now carries #52.1's weight, f_nλ^{(k)}_nwα_{1,k}L^{−k} ≤ λ_wα_{1,k}L^{−k}, as GC #6.14.1-0 used. #T4.30: #45-3's source bound now has L^{c_w}, so C_{mx} := O(1)L²(dKM₀ + 1 + KC_{rsp}M⁵C₁^{RG2})/r_B; its consumers #73, #74, #76-1, #78-3, #79 use only C_{mx}ε_k ≤ ⅛(1−β).
- From the table fork, 9 Nov 19:25: #T4.48 (K := O(C_QS_L); "K: C_Q, a constant of d (#41-1), and S_L (#T4.32)") and #T4.30 (C_{mx} := O(1)L²(…)/r_B, #45-3) entered; table dc0527160132, LABELS_LF_AND_TABLE edd42eee26fd, LF be4425381bda. Both rows read and verified against EP 1608d8f8e6f0. Closed.
- To LF, 9 Nov 19:29: D2.7's #7 (R-eval) block, lines 5–18, rewritten in place (hash-checked 0d941483552b; D2.7 now 794f19fd3b73; nothing outside the block touched). Pointers sent for 15.5: (α′)(3)'s reference point is the zero point Φ(P(𝐔)) = U_k^0(M(𝐔)) (EP #39-3, #39-7), and the s-points lie within 3C_Hα_{1,k}²L^{−k} of it (#39-3-1), so the slack check reads 3C_Hα_{1,k} ≤ 1/64; Y₁ is fixed inside D′ (#39-5-1) with the strip facts #39-5-2; line 149's "#44" is the lemma #44-1–#44-1-6 with #44-2–#44-3; its j′-average bound is #41-1's C_Q, and #96's complex data bound carries λ_w.
- From LF, 9 Nov 21:01: D27 changed 794f19fd3b73 → f37646e6ab98; LF rewrites D27 lines 3, 129, 141, 149, 165, 215, 224, 234 and 263 and asked that this session not edit them until it sends the SHA. LF accepts points (1)–(4) of 19:29 and gives the interface BP_LFR2_LOOP_LOCALISATION.md 10172ac2b33e (#BLL.31 per 𝒦, #BLL.32-2 ε_F ≤ |X(F)|e^{−R_k/2}, #BLL.4-1 no close units, #BLL.28 ℓ_c ≥ ½|𝒦|(R_k − 3), #BLL.29 δ = 1, #BLL.36–#BLL.36-3 sums over 𝒦, #BLL.34 F^∅).
- To LF, 9 Nov 21:02: the 21:01 change was this session's, line 11 only (ε_Φ → ε^{fr}_Φ twice, the stage-norm rename against CRE's ε_n = g_np₀(g_n)); no D27 edit until LF's SHA, the #7 block included; #613 (c_r⁺, η(D)) to be redone against #BLL.28, #BLL.31, #BLL.32-2, #BLL.36 after re-deriving them.
- To the table fork, 9 Nov 21:04: six rows (β ≤ 7/39 in #T3.34, #T3.39, #T4.30 with (57/64)(1 − β)λ^{(k)}_n + β/2; #T12.5's γ_S := min(α_P, 1)/2, r_S, a_S; #T2.12's 11M′ and 24LM′; contacts-draft locals not registered; #T4.47's λ_w remark deleted; #T4.32, #T4.32-0 ε^{fr}_{n+1}). From the table fork, 21:06: entered, table 911950a7d629, LABELS_LF_AND_TABLE 768a4c37c324 (verified).
- Self-review repairs 19:34–22:50 (MX, contacts draft, EP, GC, NS, TL #894, #946, NL #NL7.1-4, PF full review and §3.2-8d2 rewrite, line splits) are logged in WILSON_IT1_TWO_LOOPS_SELF_REVIEW_2026_11_09.md. Bookkeeping in the sense of the workflow except PF §3.2-8d2, MX #5.10.6-6, EP #75-2 and the contacts draft's §1 and §4a, which change mathematics and go to their next content rounds.
- To the table fork, 9 Nov 22:43: #T12.4 (s_j := 7M, s₁ := 2M_VR₁, K′_{att} at #PF3.2-8d2a-3; δ̄_D := e^{3ν_e}e^{−(3/64)ν_e(D − 8r₀)/M} at #PF3.2-8d2d-4) and #T4.52 (D_desc := 8r₀ + (64M/(3ν_e))(3ν_e + log 4) at #PF3.2-8d2e-3; N^{LF} of #PF3.2-8d3g), with the re-derivations. From the table fork: entered, table 8ed77a26f266, LABELS_LF_AND_TABLE 68912b159955 (verified: #T12.4 verbatim, #T4.52's D_desc).
- To LF, 9 Nov 22:45: D2.6 l.95 (5.3) says the step-1 extent is measured from 𝒩₁ with C_lin and no bridge gain before n_B, false under the O2′ closure §3 (𝒩₁′, factor 2 from n = 1); l.139 (7.2) bounds ε_A(1) with the superseded C_lin, harmless (2 in its place is smaller). The 101ℓ bounds of 6.2, 7.1, 7.4 are valid upper bounds (information only). D27 708b1879ff2e seen, untouched; waiting for LF's SHA.
- To the table fork, 9 Nov 22:49: #T4.32-1's three ε_{m+1} → ε^{fr}_{m+1}; #T4.48's C_* display is EP #121's, with [ν = 2]γ^{fr}_m. From the table fork: entered with "(#121; dev^ν_n and γ^{fr}_m of #117-1)" and #T4.32-1's pointer #3.2.2.1–#3.2.2.1-3; table e1c4f3f3f69e, LABELS_LF_AND_TABLE f9e665d2cd6e (verified against EP #117-1, #121).
- Self-review of NL, 9 Nov 22:50–23:05 (logged in the self-review file): #NL9.9 φ_c(b) ≤ N_CΦ_c, so N_C replaces the factor 2 in lem:two-loop-inputs(d)–(e); #NL9.6-5-1 anchors at the squares of T; #NL9.6-2 admissibility reasons; #NL10.2 B^{(N)}_W a supremum over K; PC #PC4.14-6.8.1-2–3 B_W → B^×_W. NL 0563c93b48c6, PC 6557eb3c5880, LABELS_TWO_LOOPS e6af11c3d64e. These change mathematics in NL §9 and go to its next content round.
- From LF, 9 Nov 23:00: D27 15.5 rewritten over BLL (D27 dabf9f0999a9, BLL 723394aba64e, D26 4966a47a35ca, EP 2bacaf596751, the user having allowed LF to edit D26 and EP). One more D27 formatting pass will follow (no content or label changes), with its SHA. EP: #39-3 → #BLL.8, #BLL.14-1, #BLL.31; #39-3-1 → #BLL.20-0; #39-7 σ_t of #BLL.7 (σ_t ∩ Λ = ∅ by #BLL.2), 𝐇-argument support → #BLL.6, split with #39-7-0; #127 → BLL. #BLL.19's block count is redone in PRT2 (2.46)'s distance, Σ_{y′} ≤ 8·5^ds_δL^d, C_H := O(1)s_δL^{d+8}B₀e^{O(1)κ₁}. Interface for #613: homes from K⁺ := K^{∼2} (15.0); Dep(D), h(D); D = Σ_𝒦D^𝒦 (#BLL.31); h(D) = ∅ ⇒ D^∅ = D(U^R) (#BLL.34); Σ_{𝒦≠∅}|D^𝒦| ≤ η(D) := 2‖D‖e^{ε_D}(e^{x_D} − 1) (#BLL.36-1); destinations 15.5(i-3)–(i-5); domains Y′₀, Y_P^{[1]} (#BLL.10, #BLL.33-1–#BLL.33-2); 15.8's growth 1 + η(D)/‖D‖. Point for #613: an att(k, Y) member whose home has only second-class components grows to Y_P^{[1]} at each 𝐑-step, inside the (6B) weight. Stale D27 pointers listed in TL: l.9, l.13, #295, #613–#613-3, #615, #616, #699, #728.1–#728.2, #742-1, #743, #745, #746, l.658, 687, 727.
- To LF, 9 Nov 23:05: EP edits checked and accepted (#39-3-1's BCH from #BLL.20-0; σ_t ∩ Λ = ∅ by #BLL.2, #BLL.7, and Q_m ⊂ σ_t; #127's quotes match p.374 l.37–40, p.375 l.11–12); LABELS_TWO_LOOPS e6af11c3d64e. The TL edits are this session's, in the #613 redo, against D27 by item label; no D27 edit until the post-formatting SHA.
- To LF, 9 Nov 23:25 (the message says 23:40; `date` gives 23:18 before and 23:32 after it): BLL's insertion collar λ_T = 4⌈R_k/(1024√d)⌉ + 9 lies in Y_P (B^{(m)} ⊂ A_m has s = 1 and lies in G_m, #BLL.14-0–#BLL.14-1). TL's (H0) (#509) puts it in the counted domain of every 𝐑-made insertion, about (2λ_T + 3)^d|X(D)| cubes, polylog × σ(D), at ≥ ν_r per cube. D's weight e^{ν_rσ(D)} cannot pay that for a big member, and a g-free units factor u cannot absorb it, so 15.5(i-5)'s "base share from D's weight" fails as stated. D27 15.8-1's y_p has the same defect off ⋃(Y⁺)^{[λ_K]}. Small members are fine: their collars lie in X^{(λ_T+45)} ⊂ a box of (105R_k)^d cubes, paid once per component by (1.89). Proposed repair in BLL: distance-weighted Cauchy radii e^{κ₁ + aρ(Δ,Z)}, a ≤ δ₀M/16, which give a far core an extra factor e^{−aρ(c,Z)}; with the collar λ_T only where ρ(·, Z) ≤ R_k/4, ε_D keeps its e^{−R_k/2} form and the near collars lie in per-component boxes. To be checked by LF: the class points at the enlarged radii (#BLL.21–#BLL.23-1) and #BLL.25's lengths.
- Self-review, #613 redo, 9 Nov 23:10–23:32, collar-independent part. TL #612 is now per object (BLL). #613 and #614: (β-4) and (β-5) for C₁ ⊔ C₂, with 8(104MR_k + 1)|h| bonds, |X(F_h)| ≤ 2^{d+3}·105R_k|h|, θ_F^× := 2^{d+3}·105R_ke^{−63R_k/512} ≤ 1/80, and the far-letter sum ≤ 2·10⁶MR_k. So (A), (B) ≤ ½ and a_k ≤ 11/10 for the pair, in place of "a_k at most doubles". #613-1 to #613-5: D's parts by 15.5(i-4), with D27's η(D) and the destinations (i-3)–(i-5), and |X(D)| ≤ 2N_Kσ(D), via Dep(D) ⊆ X_D ∪ ℐ(D) ∪ Z′, ≤ 3^d M-cubes per π_k-cube, ≤ 2^d per bond, and Z′ ⊂ K^{[1]}. Then 2(ε_D + x_D) ≤ ϑ_k²σ(D) by e^{−63R_k/256} = e^{−R_k/8}ϑ_k² and 8N_Ke^{−R_k/8} ≤ 1. The parts' total is ≤ ‖D‖e^{2(ε_D+x_D)} by 1 + 2(b − 1) ≤ b², and 1 + η(D)/‖D‖ ≤ e^{2(ε_D+x_D)} by (ab)² − 1 − 2a(b − 1) = (ab − 1)² + 2(a − 1) ≥ 0. Both are ≤ e^{(ϑ_k/4)ν_rσ(D)} under 4ϑ_k ≤ ν_r. #613-2-1, #613-6, #613-7, #615, #616 are deleted (BLL #BLL.9 gives the 𝐃_k domains).
- Consumers updated: #3.3, #264, #270, #286, #617, #617-1, #619, #722, #742-1, #744, #814-4-3-2, #844, #844-9, #858, and PC #PC4.14.4-4.5.4-3-1.1 (its constant part is now paid as in 15.8(c), not by #613). #844-2-1 is re-derived: η(D)/‖D‖ ≤ ϑ_k²σe^{ϑ_k²σ}, with ϑ_k² ≤ aν_r/2 and σe^{−bσ} ≤ (eb)^{−1}. That gives 1 + 2ϑ_k²/(eaν_r), so y^s_k := C_ϑϑ_k² with C_ϑ := 10/ν_r (2/(0.078e) ≤ 10; two-loop 8/(3e) ≤ 10). TL cb093381691d, PC bed57035da0a. The D_P block (#626–#647), #699-2–#699-4, #703, #714–#720, #728–#728.3 and #287's M bound wait for the collar answer; #728.1 and #728.2 still cite the old (α′).
- To the table fork, 9 Nov 23:35, announcing these rows. #T4.53: ϑ_k := e^{−31R_k/512}; S^R likewise; c_r, c_r⁺ and C_α deleted; C_ϑ := 10/ν_r and y^s_k := C_ϑϑ_k² (#844-2-1); t_k's #613-7 pointer dropped. #T4.29-3 and #T10.40-1: their #T4.53 C_α remarks dropped. #T12.2's η(D) deleted in favour of #T12.20-3-1's (TL #613-1). θ_F^× (TL #613) added beside θ_F. #T12.2's ℓ_a and ℓ_{a′} held until the D_P rewrite. Waiting for the table SHA.
- Table at 1f9b047685e4 (LABELS_LF_AND_TABLE f6d38e66e0fa), verified 9 Nov 23:34.
  - #T4.53's ϑ_k = e^{−31R_k/512}, C_ϑ := 10/ν_r and y^s_k := C_ϑϑ_k² agree with TL #613-4 and #844-2-1.
  - #T12.20-3-1's θ_F^× is right.
  - #T12.2's D^𝒦 now points at #T12.20-3-3 and TL #613-1. The fork's pointer to #728.5 for δM = 1 stays valid until the D_P rewrite moves it.
  - Confirmed to the fork.
- TL rest, 9 Nov 23:33–23:38. Repairs in place, all bookkeeping (no bound changes):
  - #265's link-position bound is now M(#_k + n_k/M) ≤ 19Mσ (#254). "(M ≥ 100)" was not its reason.
  - #295 cites BLL and #BLL.9 in place of a phrase D2.7 15.5(ii)(β) no longer has.
  - #323 adds the 𝐑-step factor (1 + y^R_k).
  - #394's rule (A2) is at V4 L3574.
  - TL 4ccd740c62e6.
- TL #338 and the PC rest, 9 Nov 23:38–23:41.
  - #338's c_d is now the map's ν/(32A_dML) (#MD2.3.5.2), not #T4.20's. Its consumers use it only as a symbol.
  - To LF at 23:40: the continuum note's #NK.4 also writes c_d = ν/(64ML) and c_E = ν/(128ML).
  - PC: ε_k → ε^r_k in #PC4.14.4-4.5.4-5, #PC4.14.4-4.5.5 and #PC4.14.4-4.5.5-1, the clash being with #T3.27's ε_k. Re-pointed: #PC4.14.4-4.5.4-0 (to #613-5 and #844-2–#844-2-1) and #PC4.14.4-4.5.4-3-3 (to #844-2-1).
  - TL 72b79488fd65, PC 3d6bdad67c21.
- BLL collar, 9 Nov 23:41 – 10 Nov 00:04. Read BLL #BLL.0–#BLL.36-3 again (723394aba64e).
  - My 23:25 proposal fails. A walk term carries s(Δ) over every cube it meets (#BLL.8-00), so radii e^{κ₁+aρ(Δ,Z)} give e^{O(1)aℓ²/M} against e^{−(δ₀/16)ℓ}. A per-core t_c on the operators' walk terms fails as well, since a composite term can hold k operator walks meeting one core (t_c^k). LF found the first failure independently (message 23:52).
  - From LF, 23:52: #NK.4 and #ND.5.3-2 fixed (continuum note 0d03170887c1). Checked: c_d = ν/(32A_dML) (map #MD2.3.5.2) and c_E = c_d/2 = ν/(64A_dML) (#MD2.3.6.11-1).
  - To LF, 10 Nov 00:03: the far-bond split. Every bond outside Z lies at sup-distance ≥ M(2R_k − t_k − 1) from the sources (#BLL.7). So at every s-point it sees the families only as a phase of at most 3C_Hα²L^{−k}e^{−(δ₀M/32)R_k} (#BLL.16–#BLL.21 with ℓ ≥ M(2R_k − t_k − 1)). The far bonds are assigned to M-cubes, and z_y multiplies the phase on cube y's bonds, with |z_y| ≤ R = e^{(δ₀M/64)R_k}. Then F = Σ_Bδ_BF, with |∂_z^BF| ≤ ‖F‖(2/R)^{|B|}.
  - The T̂-collar is then taken only around H = ⋃_{K∈h(F)}(K⁺)^{[1]}. Cores anchored at X(B)^{[1]} cost at most e^{4|B|/3}. ℓ_c(F_B, 𝒦) ≥ ℓ_c(F, 𝒦), and ε_F ≤ ε^H + |X(F)|e^{−R_k} ≤ |X(F)|e^{−R_k/2}.
  - Domains: Y_P ⊂ ⋃_{h(F)}(K⁺)^{[λ_T+1]} ∪ X(F)^{[2]} ∪ ⋃_𝒦K^{[λ_K]} ∪ ⋃_cc^{[1]}, so TL's (H0) holds with 8M. Asked LF to confirm: δ₁ ≤ 1, for δ₀M ≥ 128 by (W-M); and #BLL.22–#BLL.23 for a phase field that the families do not produce.
  - TL's D_P block waits for LF's BLL and D27 SHAs.
- LF's points on the repaired BLL, 10 Nov 02:05–02:20 (BLL 6ab8dc5ecd99, read in full; D27 a5fc6ecd872c, then 3b83d9913336, read only).
  - (a) GC #6.13-1's margin. (1 + 9x/64)(1 + x/16) leaves at least 39x/1024 below 1 + x/4, and (1 + 9x/64 + x/32)(1 + x/16) = 1 + 15x/64 + 11x²/1024 ≤ 1 + x/4 for x ≤ 16/11. #6.13-1 now records the shares: 9x_n/64 for #88.1-3 and #86.3, and x_n/32 for #BLL.22-3. #6.2-1's conjugation bound holds at the (s, z)-points, through #116.2's ε^{fr} ≤ 4λα_{1,k}, given #BLL.21.
  - (b) EP #75-2: (49/64)(1−β)λ + (8/64)(1−β) + β/2 ≤ (57/64)(1−β)λ + β/2, leaving (7/64)(1−β) − β/2 = 17/512 at β = 1/8. Correct as quoted in #BLL.21.
  - (c) The zero point. #75-2 and #127-1 are taken with the left factors at s = 1 (#90 (iii)) on U_k^0(M(𝐔)). Bałaban's (1.60) (p.372 l.24) keeps the left factor outside (1.61). So the zero point is s = 0 on σ_t for the families m = 1, 2, 3 and s = 1 for the left factors (#39-3). #39-3-1 extends #BLL.16–#BLL.20-0 to parameters on all of σ_t, as they use only that a changed cube lies in σ_t (#BLL.17–#BLL.18).
    - For the base to be U⁰, #39-5-1 now takes Y₁ := D′(X(F)^{[2]}) = Y₁⁺(F) (#BLL.4-00, #BLL.7-2), and #39-5-2 reads with X′ = X(F)^{[2]}. #39's domain clause was rewritten to match.
  - (d) The D2.7 15.5(ii)(β) cites were re-pointed to #39-5-1 and #BLL.9: EP #17, #87, #88, #113, the line after #113, #158; TL #6-1, #868-1, #870, #871. D27 l.7 waits for LF's final SHA.
  - To LF, 02:20: (a)–(d), the replacement text for table #T11.27's last sentence (it still says "smallest inside D′"), and a request for D27's final post-formatting SHA.
  - EP c224fb44747f, GC b7222a1ad74c, TL 945cff66d5ba.
- TL's D_P block against BLL c5dd02b9195d and D27 0ebe6e1f5035, 10 Nov 02:43. The case (b) members of #699-3, the whole-joined att(j, Z′) members whose T_D meets no X⁺, lost the connected-piece argument: under the component-by-component Y₁⁺(F), nothing in BLL joins the cluster of X(D) around T_D to the one around Z′.
  - Structural fact, re-derived from D26 2.1(a), §3 (l.72), and the inherited species (2.1 *Merged groups*, 4.3; TL #467–#468): dist_∞(T_D, Z′) ≤ diam_∞(T_D) + 3C_boxM in step-k units. A constituent W₀ made at step p has B_∞(n′, R_{t+1}) meeting Z′; R_{t+1} < sup_{x∈X(W₀)}|x − n′|_∞ + 2C_boxM for t ≥ 2, R_2 = 3C_boxM; n′ ∈ X(W₀) ⊆ X_D ⊆ T_D (D26 5.0, TL #617, #693); step-p lengths are at most step-k lengths.
  - So a case (b) member has diam_∞(T_D) ≥ M(2R_k − 3C_box) ≥ 42M, is big, and its segment s_D to Z′ has length ≤ (11/10)Mσ(D) for R_k ≥ 33C_box. lw members lie within one MR_k-layer of their component (D26 6.2), so they are never in case (b).
  - Case (a) with h(D) = ∅: T̂_I ⊂ X(D)^{[1]}, and 𝔊's chains run in Y_P from X(D)^{[2]} to the units, so dist(T_D, ⋃_{K∈𝒦}K) ≤ M(ex(Y_P) + λ̂ + 5) and ex(Y_P) ≥ 2R_k − λ̂ − 5 ≥ R_k. Case (a) with h(D) ≠ ∅ is an att(j, Z′) member and takes the structural fact.
  - To LF, 02:43: (0) the D27 SHA 0ebe6e1f5035; (1) #BLL.31 with e^{3κex(Y_P)} (L ≥ 3^{d+1}/2 holds), the third κ being TL's D_P's; (2) a sentence for #BLL.33-0, every cube of Y_P at d_□ ≤ ex(Y_P) from Y′₀, with its derivation, and whether a class-E anchor's K lies in 𝒦(P); (3) D27 15.4(i)'s "dom P is a connected set" fails for case (b) members; repair: the segments s_D in dom P, a fifth share for their MR_k-cubes paid by D's weight (rate κ2^{d+3}/R_k per unit of σ(D)); (4) which domain, units, and distance bound D27 gives 15.5(i-5)'s att(k, Y) parts when Y is later first-class.
  - EP bd315b140072, GC b7222a1ad74c, TL 945cff66d5ba, D27 0ebe6e1f5035, table cf22045a3f38.
- Continuum note renumbered (LF, 10 Nov; e4f4ee900f12), bookkeeping, 02:48: TL #296, #602, #604, #924 (4.5) → (4.4) (#ND.4.9); #940 (3.5), (9.3) → (3.4), (8.4) (#ND.3.12, #ND.8.6); #919 names the continuum note's (6.3); #603 deleted, as the old (4.4)'s far-component decay no longer exists and the new (4.4) is the supremum (1 − w_{ℓ₀})B_LF. PC, NL, PF cite only live #ND tags. TL 1797e77cfc3d. Acknowledged to LF.
- TL's D_P block on D27 f1798901f44d and BLL 1462b12980d4 (LF's (1)–(4) re-derived), 10 Nov 02:50–04:20.
  - Structure: dom P := ∪X′_r ∪ X̂ ∪ Y_{P′}^{[1]} ∪ K⁺; dom^♮P adds T⁺_D := (T_D)_{5M}, with s_D when ℓ_D > 2MR_k, and is connected (#629, #629-00, #630). D_P := Σ_r(d_k + 4R_k + 2λ̂ + 498) + 4Σex (#627); δ_P := diam_∞(dom^♮P) ≤ M(D_P + 2ℓ_P + (43/20)Σ_{big}σ) (#629-3, #631–#635, #698–#698-1). The counted domain leaves out the cubes near a T_D that are cubes of no X_{D′} (#629-1).
  - Consumers re-derived. ν_e ≤ ν_r/5832 makes the extent terms ν_r/1000 (#795, #798, #799, #835, #858). (H0), (H2) of 𝐑-made insertions under #629-1: E_D also holds the cubes meeting ∪dom^♮P, closed-connected, at most 65u_𝔏σ + 160 cubes (#511, #519, #521–#521-5, #524, #561, #678-1). hull(g) through dom^♮P (#832). #855–#855-1 under R_k ≥ 40/ν_r. #286's list.
  - D2.7 15.5(i-5-0)'s member shares of |P|_w: #814-4-1-1–#814-4-1-4 (at most e^{(ν_r/16)σ(D)}), charged in #732, #799, #858 (totals 0.844 ≤ 1, 0.845 ≤ 0.922, 0.691 ≤ 0.89). A cross member needs no charge: a polymer with a cross member has no span (#748), so no polynomial entropy factor sees its |P|; its shares enter only the gas sums' KP weights, inside its weight (#775).
  - Bookkeeping: 4R_k + 92 → 4R_k + 2λ̂ + 498 at #806-1, #815.2, #817–#817-1; #613-2 h₀(D) (15.5(i-5)); #658, #800 without trees; #690, #714-1 X^{(247)}; C_w → C_pw in #814-4-1-1 (C_w is #T4.22's, #T12.12's, #T12.19-1's). Lines over 630 characters split: TL #629-00, #715-1, #724-1, #817-1; EP #39-00, #39-3-0, #39-5-1-0, #88.1-00, #130-8-1-1.
  - LF's question on X_𝒟 and σ^{set} with the sets Y⁺: TL reads X_𝒟 only in #572-1, through 15.8-1(2-5)–(3-1) and the pieces' intervals in X_𝒟; unaffected.
  - D2.7 lines that quote TL and are now wrong, sent to LF: 15.8-1(1-2)–(1-2-1), (2-2), (2-3), (2-4); 15.5(i-0-2), (i-5-1); (ii)(β-2); (i-5-0)'s pointer. Table rows to the table fork: #T4.42, #T4.43, #T12.2, #T12.2-3, #T12.2-13, #T12.2-14, #T12.20-5, and new rows.
  - TL 7c0be1c752c3, EP ee90f3c43a7f, labels 7f7329ff7ac6, D27 f1798901f44d, BLL 1462b12980d4, table e712ced4f218.
  - Table fork's reply: items 1–5 applied as sent; 6–7 wait for D27; new rows #T12.2-17, #T12.2-17-1, #T12.2-18; one dom P row for TL and D27. Agreed, with the reading sent to it and to LF: D27's "a polymer meets a second-class or unchanged component" (l.320, l.396, l.542, l.791) is Bałaban's c₁ criterion, a localisation domain meeting ∪Y_i (LFR II p.390 l.2), as TL #800 and #816-1 read it, not dom P ∩ ∪Y_i ≠ ∅.

- 10 Nov 2026 04:56–05:22, PF (CV) and the peers' checks.
  - D27 15.8-1(1)–(7) at 493ce3705d5d verified against TL 7c0be1c752c3. Sent to LF: (1-0) should cite Dep(F) ⊆ X(F) ⊆ Y₁⁺(F) ⊆ Y_P (#BLL.4-00, #BLL.14-1-1). LF's repair at 35045b800482 ((1-0), (1-0-1), through X(F)^{[2]}) verified: h(F) ⊂ 𝒴 by 15.5(i-2)–(i-3), and B(F) ⊆ S_𝒟.
  - Table 8ef0b22a86eb: rows #T4.42, #T4.43, #T12.2, #T12.2-3, #T12.2-13, #T12.2-14, #T12.2-17, #T12.2-17-1, and #T12.2-18 re-read; they agree with TL. The table fork entered #T12.4-1 and #T12.4-2 (table 1f9c36049da1) and reported the clashes s₁ (#PF0.2 against #PF3.2-8d2a-3), F_i (#T4.55), t_k (#T4.53, #T12.17), and R.
  - PF renames (bookkeeping): #PF0.2's s_i → ℓ_i^{ph} and R → D^{ph} (#PF0.2–#PF0.5-2, #PF4.3-3); F_i → O_i and t_k → D^{(k+1)} in §4. Sent to the table fork with the rows to update and the new symbols 𝒵_i^{(k)} and f_i^{lf,(k)}.
  - PF §4, repaired in place. The old #PF4.2-2.2 (norms are averages), #PF4.2-2.3, #PF4.2-2c, #PF4.2-2d, and #PF4.2-2d-1 are replaced by: #PF4.2-2.2, the large-field part f_i^{lf,(k)} on 𝒵_i^{(k)}; #PF4.2-2.2-1–#PF4.2-2.2-2, on 𝒵_i^{(k)} the fields near C_i are integrated only inside 𝐓_k (CRE p.257 l.56–p.258 l.2, (2.21) p.258 l.19–35, Ω₁ ⊃ ⋯ ⊃ Ω_k p.254 l.47–50), which is not expanded, so Jensen gives only 2‖O_i‖_∞𝐏(𝒵_i^{(k)})^{1/2}; #PF4.2-2.3, what is missing (‖f_i^{lf,(k)}‖₂ ≤ ½C_{os}ρ_{cv}s_i^{(k)}(1 + s_i^{(k)}) and the step decorrelation on 𝒵_i^{(k)}, bounds on the V_k-dependence of 𝐓_k beyond its size); #PF4.2-2c–#PF4.2-2d-1, the small-field parts.
  - #PF.1 split into #PF.1 and #PF.1-1, and #PF3.2-8d3c into #PF3.2-8d3c-1 (643 characters). Size 40922 → 42.9k characters, from the new large-field lines.
  - BO99 checked for the same structure: "the large field part given by the integral operator T_k(Z_k) associated with unperformed integrations" (p.515 l.14–16). Its large-field terms in the two-point function decay only at the final scale, and they are small because β_k → ∞ (p.516 (4.9), p.517 l.3–12). In YM₄, g_k does not decrease toward the infrared, so that route leaves a term that does not decay in D.
  - Rechecks: §0, the §3 split, and §4, twice. Every PF tag resolves, and every line is ≤ 600 characters.
  - Raised with the user: the target of §4 (the large-field part needs new estimates on 𝐓_k).
  - PF 69df480e05d7 → deb8a64033a9; D27 35045b800482; table 1f9c36049da1.

## 10 Nov 2026 08:44–09:14: PF §4, attempt on (CV1)–(CV2)

- New, derived: #PF4.2-0a. 𝐏 = w₀𝐏_{ℓ₀} + (1 − w₀)𝐏_{lf} gives Cov_𝐏 = w₀Cov_{𝐏_{ℓ₀}} + (1 − w₀)Cov_{𝐏_{lf}} + w₀(1 − w₀)(x₀ − x₁)(y₀ − y₁), so |Cov_𝐏 − Cov_{𝐏_{ℓ₀}}| ≤ 6δ_LFB^{(1)}_WB^{(2)}_W. This removes every large-field label of the steps ≤ K′, and with them the unexpanded 𝐓_m near C_i. (CV1)–(CV2) and the martingale are restated under 𝐏_{ℓ₀}, where O_i is a function of V alone (#ND.2.3).
- Large-field part (#PF4.2-2.2–#PF4.2-2.3-2): the event 𝒩_i (a step-m test (2.17) fails near C_i, K′ < m ≤ K) is an event of V. L² contraction gives the large-field halves of (CV1)–(CV2) once 4B^{(i)}_WP_𝒩^{1/2} ≤ C_osρ_cvL^{−j(C)} and 16B^{(1)}_WB^{(2)}_WP_𝒩^{1/2} ≤ C_cvρ_cv²L^{−2j(C)}e^{−κ′N_s/2}. (11.1) gives P_𝒩 ≤ e^{C_K + C_ℰN_s⁴}sup exp(−A(U_{K′}(V))/g_{K′}²). Open: the action lower bound behind LFR II p.380's factor for χ_j^c(P_j), applied at m > K′ to U_{K′}(V) (outside the step where LFR II uses it), and the ḡ-dependence of B_LF.
- Small-field part (#PF4.2-2c–#PF4.2-2d-0): #C8.5.1 multiplies by C_mc ≥ 1 per step, so its iteration does not decay; open: the gain per step.
- Target #PF0.5-1 gains the additive term 6δ_LFB^{(1)}_WB^{(2)}_W (raised with the user).
- Pre-check: every changed line of §4 reread; symbols checked against the table and PF §3 (renamed to avoid E₀, N_i, P₁, π); every internal tag resolves; lines ≤ 610 characters. Table rows #T12.4-1–#T12.4-3 stale: table fork told 09:12 with the replacements.
- PF deb8a64033a9 → 061d54eaed70 (45 989 bytes).

## PF §4 closed by the typical action (10 Nov 2026 09:20–10:02)

- The martingale route (#PF4.2, #PF4.2-1–#PF4.2-2d-1, old #PF4.3–#PF4.3-3, (CV1)–(CV3), 𝒩_i, P_𝒩, C_Cov, C_mc) is deleted. It is replaced by a direct bound at K′.
- #PF4.3: 𝐏_{ℓ₀}(A(U_{K′}(V)) > T_tyg_{K′}²) ≤ ε_{K′}²/(9N_s²), from (11.1), #C11b.1-1 and #ND.3.4-1.
- #PF4.3-2–#PF4.3-5a: on the event, every plaquette of V is within (2/3)ε_ty of 1 and U_{K′}(V) is in VAR's space at B₃ε_ty (balaban_proofs/BP_PF_ACTION_LOWER_BOUND.md #BPA.6). The coarse loop is bounded by the lasso and V4's Lip_χ, and β by the map's (7)(a)–(b) with t = c_hB₃ε_tyη². So |W^{ℓ₀}_i − 1| ≤ c_tyℓ_i²ε_ty + ι^{ℓ₀}_i.
- #PF4.4: by Cauchy–Schwarz, |Cov_{𝐏_{ℓ₀}}(O₁, O₂)| ≤ 4|e^{E^{(1)}+E^{(2)}}|ε_{K′}²ℓ₁ℓ₂/N_s² ≤ |e^{E^{(1)}+E^{(2)}}|ρ_cv²ℓ₁ℓ₂/D². #PF4.5 shows the conditions hold for ḡ ≤ ḡ_ty, using 2p₀ > 8r + 1 and ι^{ℓ₀}_i = O(ḡ²·polylog). #PF4.6-2 gives the relative form 16ε_{K′}²(ℓ₁ℓ₂/N_s²)|𝐄O₁||𝐄O₂|.
- B_LF's ḡ-dependence and the small-field gain are no longer needed. |W_χ| ≤ 1 bounds W^{ℓ₀}_i on the support.
- #PF0.5-1's first term changes from C_Covρ_cv²ℓ₁ℓ₂/D² to |e^{E^{(1)}_{const,K′}+E^{(2)}_{const,K′}}|ρ_cv²ℓ₁ℓ₂/D², because B_E is polylogarithmic in ḡ^{−1} (#T4.37). This is raised with the user. The bound is D-independent smallness, not decay; #PF.1, #PF0.4, #PF0.5-2 and #PF0.5-3 say so.
- TL #941 and #943 now point to PF. BPA's pointer is now #PF4.3-3.
- Pre-check: every changed line was reread twice and every cited tag looked up (#ND.2.3, #ND.3.4-1, #ND.5.4-2, #ND.5.6-1, #NWTF.1, #C11a.10, #C11b.1-1, #C11b.3, #C11c.7-2/3, #CK.1-19, #CP.21, #MOMST.9-2, #MOMST.75–#MOMST.83, #MD2.0.2.6–7, #T3.27, #T3.32-2, #T3.33, #T6.23, #290, #332, #334, V4 L225). CRE p.244 l.25 confirms the action normalisation used in #BPA.5. New symbols were clash-checked. Lines ≤ 544 characters, LF endings.
- Table: the fork was told at 10:00 to delete #T12.4-1-1, #T12.4-2 and #T12.4-3, retitle #T12.4-1, and add the §4 and BPA rows.
- PF 061d54eaed70 → 581440a50887 (44 835 bytes before the last two in-line edits). TL 7c0be1c752c3 → a9b39148cb5c. BPA feff3e4b6b03. LABELS_TWO_LOOPS 29a41a1cd36b.
