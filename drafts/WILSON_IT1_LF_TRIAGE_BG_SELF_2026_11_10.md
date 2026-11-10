# Background-Iteration Closure, Session Self-Review (10 Nov 2026): Triage

Review: the session's own full read of WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md at 21f190678787, every line from the opening to the closing lists (user, 10 Nov 2026: a session's own full review counts as a round).

## Verdict

Not clean. There is no fatal and no serious finding, and there are fifteen minor findings (F1–F15); F14–F15 were found while indexing the note's definitions in the table. Every tag resolved, and λ_* agrees with #T3.37.

## Repairs

- **F1** (opening): "the ratio of the two normalisations is N_k" was imprecise; it now reads: the ratio over the steps k+1, …, K is ∏_jr_j, the explicit factor of N_k in §3.1.
- **F2**: pointers "§1.1" to the definitions now cite *What the Objects Are*.
- **F3** (§3.1 *The complement*, the opening, §3.2, (iii-b)): the coarse D(K) form on 𝔏_good needs (iv-a)'s attached species, and the complement paragraph contradicted §5.3's carrier result.
  - Repair: the coarse chain has the form given (iii) and (iv-a)'s attached species, its leading word needing no carrier species (§5.3 *The carrier item*). The labels kept out of 𝔏_good are those on which the map's (7)(b)–(d) fail, or on which a scale-k block of a bond of C meets Ω_K^c (§5.1(b)), or which leave B(Γ_{j+1}) at an intermediate step (§5.1(a)).
  - R_bad is then the whole-label content of (iv-a)–(iv-c) and (iv-e), and not a further interface. §3.2's third term and (iii-b) cite (iv-a) for the attached members.
- **F4** (§4.2, *What Is Bałaban's*): the abelian sharpness sentence was not proved; it is deleted, with "and its sharpness in sup norm" in the derived list. §4.2 is split at sentence boundaries.
- **F5** ((iii-c)): the stale conditional "If the parallel derivation…" is replaced by the coarse-chain note's §6, which restates a1–a6 for the composed species with the slot amplitude ε_H^{(k)} and the arc I^{(k)}(G), to be verified and reviewed (the opening list).
- **F6** ((iii-a), §5.3 (4), *Constant Conditions*): the note's ε_H^{(k)} := ε_H/(1.12(b_d^c)^k) clashed with the coarse-chain note's ε_H/(b_d^c)^k, and §5.3 (4) used an undefined O(1)h_j.
  - Repair: ε_H^{(k)} := ε_H/(b_d^c)^k, the coarse-chain note's. The factor 1.12 moves into the new k-independent condition (Cε) 1.12c_π′c_CM·O(1)·4B₀e^{16κ_s}ε_H ≤ 1, with RG2 p.6's O(1) ≥ 1 (#MD2.1.4.27-2).
  - (iii-a)'s per-cube count: |𝐇_Y| ≤ 4B₀e^{16κ_s}ε_H^{(k)} on the polydisc |t_YB′|_Y ≤ ε_H^{(k)} (#MD2.1.4.4-1, RG2 (1.18) p.6); at most 1.01c_CML^{j−k} scale-k bonds per π_j-cube (coarse-chain note §1.2(ii)); ηL^k·L^{j−k} = 1; 1.04·1.06·1.01 ≤ 1.12; (b_d^c)^kε_H^{(k)} = ε_H. So the exponent per cube is at most 1.12c_hc_π^ℂc_CM·4B₀e^{16κ_s}ε_H ≤ 1 under (Cε), as c_hc_π^ℂ ≤ c_π′ (#T12.13-1, #MD2.1.4.27).
  - §5.3 (4) uses O(1)·4B₀e^{16κ_s}ε_H^{(k)} and cites (Cε); the stray "(α)'s" is removed. (Cε) implies #MD2.1.4.27-1, #MD2.1.4.27-2 and the coarse-chain note's (C7), since c_π′ ≥ 2c_πc_h.
- **F7** (§5.3): "(C9)" now reads "the coarse-chain note's (C9)", which holds off Ω_j as stated there.
- **F8** ((iii-d)): the curvature is ¾ε_h(L^{j−h}η)² = ¾ε_hL^{−2h} per fine plaquette (#5.6-1).
- **F9** ((iv-e)): the quote of the Cauchy note is #C11.1 and the pointer for Ω_n^c ⊂ Z_n is #C11b.1-5. The two-loops session had already made the first change (see *Merged edits*).
- **F10**: the constants are renamed to the table's C^E_Σ, C^T_E and c^T_E.
- **F11** ((iv-b) sum, §5.2): p₀(g) = (log g^{−2})^{p₀} is LFR II's, without A₀ (#T10.2-1).
- **F12** (*Sources Read*, *What Is Bałaban's*): both lists were incomplete, and the old closing line repeated the derived list.
  - Added to Sources Read: CRE p.247 (1.5)–(1.6) and pp.257–258 (2.18)–(2.23); LFR I p.176 (0.3); LFR II p.384 (the factorisation and (1.80)) and p.387 (1.89); BETA Lemma 2.1(i); the pair note's #NV.3-4-2 statement; Cauchy #C7.6-7-1; the coarse-chain note's §1–§4, §6, §8 and *Constants and Conditions*; D26 §8; the table's #T3.37, #T10.2-1, #T12.16; TL #6.2, #6.14-0, #222-2; the map's (g) #MD2.0.5.40, #MD2.0.1.6, #MD2.0.3.52-1, #MD2.1.1.27, #MD2.1.4.4-1, D2.4(4), (6), (10)–(13).
  - The page numbers were read in the transcripts: LFR II (1.79) p.383, the factorisation, the estimate by exp(−2p₀(g_k)) and (1.80) on p.384, (1.89) p.387; LFR I (0.3) p.176.
  - *What Is Bałaban's* has a bullet for CRE (1.5)–(1.6), (2.18)–(2.23) and LFR I (0.3); an *accepted* bullet for LFR II p.384, (1.80) and (1.89); RG2 (1.17)–(1.18) among the map's quotes; and a bullet for other notes' results used as inputs. The old closing line is folded into *Inferred, not printed*.
- **F13**: 44 lines exceeded ~600 characters. Every line edited in this pass is split at sentence boundaries; the lines this pass did not touch, and single sentences over 600, are listed in the session's report to the user.
- **F14** (state a fact once): the note defined b_d, b_d^c and a_d both in 4.1(4) and in (C1), C_{A,n} and C_{A,1} in (iv-e) and in (W), C^g_{A,n} in §5.3 and in (W^g), and X_c in §1.3 and 4.1, and it restated as its own definitions the map's w_j (#MOMST.86), the D2.6 closure's V_i^*, the Cauchy note's Z_ℓ (#C11a.1-1) and the coarse-chain note's c_X.
  - Repair: one definition per symbol. 4.1(4) and (C1) cite table #T12.13 for a_d, b_d and b_d^c (a_d = 7.2 and b_d = 69/9 at d = 4); (W) and (W^g) cite (iv-e)'s and §5.3's constants; 4.1 extends §1.3's slot, which is 4.1's at s = 1 (#MD2.1.1.23-1) and a′ = 0.
  - w_j, V_i^* (#T12.19-12), Z_ℓ and c_X (the coarse-chain note's §4.4) are now cited as the sources' quantities. The second V of §4.2 is named as the complex-data analogue of the first.
- **F15** (clash within the note): (iv-e)'s e^{c_C} used the name of the map's contour constant c_C = 4 (#MD2.0.5.30), which the note uses in c_CM. The consumers (the map's #MOMGD.2, the pair note's #NV.3) cite e^{c_C}, so the name is kept, and (iv-e) says that its c_C is not the contour constant.
- **The modulus of κ_f^{(K)}** (two-loops request, re-derived): W_χ is complex for a non-self-conjugate π, so κ_f^{(K)} is not known to be real-positive. Every bound on a modulus now uses |κ_f^{(K)}|: §3.1, §3.2, §3.4, (iv-b), (iv-e) and §5.3. Also |N_kκ^{g,(K)}| = |κ_f^{(K)}|e^{Re E^f_{const,k}}.
- **𝐇_j(0) = 0** (§2.2): the citation is RG2 (1.18), p.6.

## Merged Edits from the Two-Loops Session

The two-loops session edited the note while this pass ran (it confirmed the four edits). Each was re-derived and kept:
- (iv-e) quotes #C11.1.
- (iv-e)'s e^{c_C} := exp(4Cℓ_C(ρ_Kε_K + τ_K²) + r^R_K), with r^R_K inside c_C.
- The factor 2 in the ℒ_K bound 2|κ_f^{(K)}|e^{c_C}δ_LF.
- §3.4's term with that bound.

## Pre-Check

- Every changed line re-read after the pass; every use of ε_H^{(k)}, (Cε), κ_f^{(K)}, (C9) and the ℒ_K bound grepped and made consistent.
- The note's ":=" definitions grepped against the table (bgclash, tbclash) and within the note (bgdefs): after F14 every symbol except §4.2's local V is defined once.
- The table's new rows #T12.30 and #T12.30-1 to #T12.30-10 index the note's definitions. Clash notes cover the identical names X_c, N_k, x_k, w_K, Δ_i, Z, 𝐔, G′, m̂, c_X and c_C. They record the identifications Ξ^f_j and r_{j+1} with #T12.13, C^R_1 and R̂_K with #T4.52 at K′ = K (TL #886), Z_ℓ with #T12.7, and V_i^* with #T12.19-12. The rows were announced to (4) before the edit.
- Table checks after the relabel: defcheck 0 lines; dmarks2 16 unentered candidates (unchanged); deadcheck and prefcheck show only their earlier hits; columns 8×5, 74×6 and 267×7.
- Every tag resolved against the map, the table, TL with BP_TL, Cauchy and the continuum notes (bgptr); the remaining hits are the known non-tags #cubes and #X.
- Size: from 295 lines (21f190678787) to 332 lines and 100,439 characters (521bd90aaecd). The growth comes from the line splits, F6's per-cube count and (Cε), and F12's lists. F14 removed text.

## Defects in Other Sessions' Files (sent to their owners)

- Coarse-chain note (owner (4)): §2.2's exponent, (C7) and (C9) lack the factor 1.04 of ‖log V‖ ≤ 1.04Δ_k. c_π itself is right for the norms of π-images (the second self-review, WILSON_IT1_LF_TRIAGE_BG_SELF2_2026_11_10.md G3). So (C7)'s 1.08 should be 1.12 and (C9)'s 1.06 should be 1.11. (Cε) implies both the printed and the corrected (C7).
- The map, near #MD2.3.4.17-2 and #MOMST.93-11, and the continuum note quote the ℒ_K bound as κ_f^{(K)}(e^{c_C} + e^{Re E^f_{const,K}})δ_LF; (iv-e) gives 2|κ_f^{(K)}|e^{c_C}δ_LF (reported by the two-loops session; relayed to (4)).

## SHAs

Background note: 21f190678787 → 521bd90aaecd. Table: 3863071c0dad → 71ffeded3d9d. LABELS_LF_AND_TABLE: 64f00adb209d → b925098483ec (relabelled at LF 94d3e82675b1).

## Status

This pass is a round with minor findings, all repaired. The next full self-review of the note is the candidate for clean round 1; a second clean full round must follow.
