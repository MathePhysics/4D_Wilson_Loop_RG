# Triage of review round 23 on the D2.6 closure (25 Oct 2026)

Reports: verification/isolated_reviewer/reviews/it1-d26-{s2,s4,s5,s6,s7,s9}-20261025-r4/review.txt (claude-opus-5-5, xhigh). Each report read in full. Closure: WILSON_IT1_D26_CLOSURE_2026_10_24.md (repairs from 02:42, 25 Oct, date). No fatal finding in any report.

Status words: *repaired* (text changed, derivation given there), *relabelled* (no new mathematics), *OPEN* (stated in §8), *moot* (the item's object was removed by another repair).

Alongside the triage, the readings were checked against their sources (the user's question "Why do you keep clasifying things as readings when you could have checked them?"). Results: R-avg, route (a)'s former readings (1)–(2), R-st and R-fr are derived or found printed; R-src is split into a printed real part and a derived complex part, the latter after an amendment of the ω-radius (below, s2 n-1).

## s9 (§9, the band cubes)

- S-A (𝔹_i(Ω) and 𝔹_{i+1}(Ω) live on different lattices as printed): repaired in §9.3. All sets are put on the one fine lattice T_ξ, ξ = L^{−(i+1)} (option (ii)), justified by p.269's own combined set; Ω′_n := Ω_n ∩ Ω_n(Ω) is the intersection of the global nested sequence with p.256's 𝔹_{i+1}(□′^{∼4}) sequence.
- Readings (1)–(2) of route (a): derived after reading their sources (RG1 (0.21) p.256, CMP98 (42)–(43) pp.23–24, VAR Thm 1 p.279, Prop. 9, (172), (190), [14] (1.65), Lemma 1). O1 is closed; route (b) is not needed.
- C_9 corrected to 4 + 4c₁₂B₃ (log factor 2, [12]'s c₁₂); condition A₁/A₀ < 1/(20B₃C_9); far term ≤ (1/40)ε_i; δM₂ ≥ 4 dropped.
- m-a, m-b, m-c, m-d, m-e, m-h, m-i, m-j, m-k, m-l: repaired (§9.1–9.4 and map l.336, l.364, l.1354). m-f, m-g: moot (R-avg derived, O1 closed).

## s2 (§§0–3)

- S-1 (R-fr posed outside the printed scope): repaired by reading the sources. [I]'s fluctuation radius equals its support radius ((I.6.34) = RG2 (1.34) p.9, |B| < ε₁/g_k; RG2 (2.3) p.12, the cutoff ε₁/g_k; RG1 (2.9) p.266). CRE p.277 l.39–44 bounds H′(Z₀), an integral over the support whose integrand includes these terms. So the bound on the support is a step of Bałaban's printed argument. CRE's p₁ occurs only in (3.43) and is undefined in CRE; LFR I's p₁ (p.183) belongs to a later, different cutoff. The phase reading of (3.16) is Bałaban's own (RG1 (2.9) with RG2 (2.3); LFR II p.380). §2.3 rewritten; label names R-fr as Bałaban's p.277.
- S-2 (arc-only (ii) sent groups with a component in Ω_kᶜ to (a)): repaired. (ii) now reads "every component of its polymers lies in Ω_k and every traversal of I(𝒢) lies in Ω_k"; rule change (4) and §4.3 amended. Such groups contain a cube of Ω_kᶜ ⊆ Coll_{k+1}, so §4.3's collar form applies. SW §1(a1)(ii) to be amended to match (SW closure, below).
- n-1 (complex σ_k): repaired, and it exposed a design failure, now repaired. R-src at real data is printed: (3.25)'s completed square (p.270), p.276, p.272's filing into 𝐁^{(k+1)}, and (2.41)–(2.42) (p.261), which state the bound for every value of A, with Theorem 1 (p.262). The complex part is not Bałaban's, since he never complexifies A. At the map's radius r_{ω,k} = c_ωε_k/g_k it fails: the source phase per boundary bond is r_kr_{ω,k} ~ (log g_k^{−2})^{2p₀} ≫ 1, and χ^{(k)} blocks a complex mean shift. **Amendment (for review):** r_{ω,j} := g_j^{1/2}, j ≥ 1. The phase factors are then local activities of size ≤ 2C_KA₁g_k^{1/2}(log g_k^{−2})^{p₀} added to Bałaban's real expansion (normaliser included), and KP holds for g_K small. The radius is used only as a domain (no Cauchy estimate in ω). Its other users were re-checked in §2.2: membership; *Propagation*, via CRE (2.6)'s g_j ≥ g_k(1+β′(k−j))^{−1/2} and the decay (2θ)^{k−j−1}; the slot-value move, via e^{−R_j}. The map's D2.2(6)(e) *The radii* is amended. The 𝐏^{(k)} bound now cites RG2 Lemma 2 ((1.41) on (1.34), p.11), and the membership names (4)(f) with R-m, R-dec, R-adm.
- n-2 (ρ_{t,k+1} in B_{k+1}(Z)'s middle member), n-3 (D2.4(6)(ζ)'s entailment), n-5 ((i) read structurally), n-6 (sup over the support, not (3.43)'s domain), n-7 (§5.0's scope extension named in 2.1(a), 2.2), n-9 (inherited wrap(j) members in *Merged groups*, D2.0(3)'s order), n-10 ((ii-w) at U_{k+1} named in §3), n-11 (𝒬^{∼5}; "weighted sum"), n-12 (header; sources), n-13 (register qualifiers), n-14 ("per component"), n-17 ((11)(b)): repaired.
- n-8 (wrap amplitude max(ρ̂_j, b_j)): repaired in 2.1(e); map (5)(g) to be amended.
- n-4 (cite CRE p.261 (2.41)'s X ∩ Z_j^∼ ≠ ∅ in R-𝐁's basis): to do with R-𝐁's source check (below).
- n-15 (N_j's rate ≤ c_* for the base M_j ≤ A_j(Z)): with s5 m-6, s7 m-e (below).
- n-16 (stale map context): with the map pass (below).
- Q1 (§3's weights given (ii-w) at U_{k+1}): agreed; labelled.

## s4 (§4, kind (γ))

- S-1 (4.3's species order contradicted 2.1): repaired. A kind-(γ) group containing an inherited att/lw/wrap member, touched or not, takes the first inherited species. Its bound is (T2) with R-src and 4.2's factors, and its sum is (T0). Rule change (3) is restricted to groups with no inherited member.
- m-1 (one split for both cases): repaired with a per-case split. (γ1) uses (¼, ¾), as in 2.2; (γ2) uses (½, ½), with dist ≤ 2M·ext and ext^{coll} ≤ ext + 1. C is enlarged by e^{ν_e/2}.
- m-2 (4.3's label cited the withdrawn r_k < c₄₃p₁): repaired. The label now cites R-fr (Bałaban's) and rule changes (3) and (4). Following the Q1 observation, R-vac(i′) is dropped from 4.3's label: the re-run at b_k ≤ Cρ_{t,k+1} covers every att(k+1, coll) kind-(γ) group, so the parity gain is not used.
- m-3 (R-dec⁺'s B-range unchecked): repaired. VAR (172), p.305, gives the range |B′| < 2C₁ε₁ with ε₁ ≤ a₁ free; (77), p.290, is VAR's internal smallness. Condition: the constant condition ε_H ≤ 2C₁a₁, which does not depend on the coupling. The wording "(190) is linear in B" and "ε_H < ε₃" is fixed. The layer bound of R-dec⁺ still rests on R-dec (inherited reading, to be checked against its source).
- m-4 (4.1's case (B) attribution), m-5 (the shrunk ε_H replaces ε_H everywhere; 4.2's label lists the ε_H conditions): repaired; map D2.1(4) *Constants* to be amended.

## s5 (§5, the carry lemma)

- S-A ((T0)'s per-position bound; the reason "at most one att interval through a traversal" was wrong): repaired. Positions of re-run vertices are defined from their new constituents and dev members only. Every link to a fixed D is rooted at D: D has ≤ 81Mσ(D) positions charged to b(D), and the root factor is paid from D's reserve (C_b). The per-position sum is the rooted animal sum, ≤ C_Mb_n·pl + K′b_n/ᾱ_n, independent of 𝔅. The round-22 and round-23 reviews agreeing on the old sentence was no proof; the reviewer's counterexample is concrete (L^{n+1−j} att(j) intervals in one traversal).
- m-1: repaired with s4 S-1 (§4.3 species). m-6: repaired with s4 m-1 (per-case split). The rate check of A_j's terms goes with s2 n-15 (below).
- m-2 (extent undercount in (T3) and 5.5): repaired. E′_𝒢 is the full ν_e-share, which bounds the spread of the vertex supports. Each non-first member adds σ(D′)/L, paid from its reserve once, at the merge. (T3)'s factor gains e^{a}. In 5.5, LE′ ≥ P gives the same rate e^{−(25/8)(ν_e/L)R}.
- m-3 ((T2)'s c_n): repaired. c_n := c̄_*b_n/ᾱ_n with c̄_* := max(2K_β, C″), from the sum rooted at D. c̄ := e^{(3/8)ν_e}c̄_*sup b/ᾱ and C_δ := 2 (5.0, 5.3, 5.5).
- m-4 (D2.0(5)'s users of the coupling upper bound): map amendment, in the map pass (below).
- m-5: repaired with s2 n-7.
- m-7 (cosmetics): C_b = e^{3/2} and ᾱ_n's min(C₀, C₁) are fixed; the "=" in 5.5 went with m-2's rewrite. S_R's index range m ≤ N is kept: it is larger than needed and harmless.
- m-8 (labels): 5.1 now names the ω-polydisc propagation with R-𝐇 and R-𝐇₀; 5.3 names R-dec⁺, R-fr, R-𝐇, R-𝐇₀ and the ω-radius amendment; 5.5 names §2.1's precedence.
- m-9: (T1) now covers the ω-route, through blocks within one π_n-cube. 5.5 states that M-free merges add no mass.

## s6 (§6, lw(Z) and the label sum)

- S-A (R-st not a reading; class (III) beyond the printed joint chart): repaired by derivation (25 Oct, §6.1). The real stencil phases are ≤ τ_b/2 by (B1)(i) and Lemma c4-10-5 (tree gauge). The complex move is ≤ Cα_{1,1}/L. Class-(III) arguments are ≤ 4c_Aε₀ ≤ θ₀ by Lemma c2-fibre-smallness(ii), far inside the joint domain ‖A‖ < 2θ₀ of §c4-10-1, not at ϑ_*/2. So R-st is derived, and C_III holds at complex data. The sharper bound ‖Y_i‖ ≤ 16√2C_πc_Aε₀ is recorded; 6.3 and 7.1 keep C_III.
- S-B (ω-dependence of the lw slots): repaired by route (b), with the convention at j = 0 in slot variables (**amendment for review**; map D(1)(iii) and D2.2(6)(e) l.936 to be amended). On S₁^* the outer variable is CRE (1.15)'s A = Ψ_ξA′; the cutoff values ω_b are frozen real factors, as the map already does for j ≥ 1 (l.813, l.216). Class (III): ‖A‖ ≤ 4c_Aε₀ + C_𝖢′g₀ ≤ θ₀ on the r_ω = 1 polydisc. Class (I): ‖Y_i‖ ≤ C_I″g₀(r+1).
- M1 (the "Consequently" clause outside its scope): repaired; the proof of (a) is cited, as extended by §3d(2)(d) *Conclusion* (IT-1 l.795).
- M2: repaired (A^fin_cov iff classes (II) and (III) are empty and no class-(I) input bond lies in J(Λ)).
- M3: repaired (V3 L462's remark; D(Λ₁) = I and E_{Ω,*} = I ⊔ J from V3 L2223, L2336, checked).
- M4: repaired (CRE (1.12), p.248, read: U = V₀ on Ω₁ᶜ).
- M5 (complex m̂ bound unsupported, C_ρ without source): repaired by derivation in 6.3 *Complex bound* (a)–(d). The local inverses are Neumann series around the real G_Δ in the weighted norm ‖·‖_{μ_H/2}, with the entries of H_𝐔 − H_{U₁} from IT-1 §3e(3.1), (3.12). The result is h_ℂ(m̂(𝐔)_b) ≤ C_m^ℂϑ_Vr, and the difference m̂(𝐔) − m̂(U₁) has (c5-5-1)'s decay form with C_Δρ₁. This needs ℓ_s so large that e^{μ_Hℓ_s/4}q_s^ℂ ≤ 1/2 (**amendment of IT-1 §3j(1)'s choice, for review**; a constant before the coupling) and the coupling thresholds σ_γC_Eρ₁ ≤ 1/2, C_Eρ₁ ≤ 1 (§8). C_ρ is gone.
- M6: repaired (the citation is now 6.3 (a) with §3i(4) and §3e(3.1), (3.12); both labels list them).
- M7 (the shift convention): repaired, and it exposed a gap, now **OPEN as O4**. D(1)(iii) is factorwise, and every carried factor is continued with m̂(𝐔). The lw slots are covered. For the carried t > 0 species, IT-1 §3j(6) bounds the frozen-centre representation (centre tm̂(U₁)), which agrees with the species only at the base point. The continuation's bound under a complex centre is not derived. §8 states what is missing and what closes it, and IT-1 l.1757 is annotated.
- M8: repaired (only π(T_i) occurs between slots).
- M9 (the "2a_lab" step): repaired. With s7 S-B's second factor 2 per ℓ-cube, 4^{#ℓ-cubes(X)} ≤ e^{3·2^dlog 2(d₁′(X)+1)} is paid from Pol(X) of 7.1's ledger, Pol := (K₁ − 2B − K₁/4 − 3·2^dlog 2)(d′+1) ≥ (K₁/2)(d′+1) under K₁ ≥ 8B + 12·2^dlog 2. a_lab and §3j(6)'s count check are unchanged; 2a_lab is removed everywhere.
- M10: repaired (O2′ widened to the later-step carry of the retreat slots, linked to O2 and IT-1 §3d(4)'s case D2(d), l.866–869).
- M11 (p.384 at d′ = 0): derived, not a reading. RG1 p.257 defines d′ as the length of the shortest tree graph, with an edge-graph form. An edge meets ≤ 3·2^{d−1} cubes, which is p.384's inequality for d′ ≥ 1; at d′ = 0 the tree is a vertex, which meets ≤ 2^d cubes.
- M12: repaired (CRE's exponent renamed r_C). M13: repaired (c_C = 4L).
- M14 (budget): repaired, and it exposed an **overspend**. 6.5's ledger omitted the complex factor e^{C′𝔰ρ₁} ≤ e^{η𝔰/8} of IT-1 §3e(4) (l.1040). With V3 L2806's θ° ≤ νσ/16 (checked), the ledger is 1/16 + 2 + 3/2 + 1/8 + η_w/η_V ≤ 4, so **η_w := (5/16)η_V (amendment for review; it was 3/8)**. (iii)'s complex rate is then 61/16 − 2 − 3/2 = 5/16 = η_w/η_V. §3a(6)'s booking of 1/8 for θ° is slack, and the ledger uses V3's 1/16. Consumers rechecked; the map is amended (map pass below).
- M15: repaired (the re-run (T0) uses no compatibility between fixed members; each lw slot is a fixed member with σ = 2^d).
- Map (ii′-c) bullet: with the map pass (below).

## s7 (§7, reviews/it1-d26-s7-20261025-r4)

- S-A (which M; j ≥ 2 uniformity): the j ≥ 2 part is resolved. VAR p.277 fixes R₁ and M₁ before the coupling, and RG2 p.3 has R₁M₁M⁻¹ ≤ 1, so the π-side M is Bałaban's constant M, and the comparisons at j ≥ 2 are uniform. 7.1 *Which M* and §1 are rewritten. The check exposed a **design failure, now OPEN as O5**. Round 22's premise M ≥ 2R₁M₁ with CRE's growing R₁ (CRE (2.5), (2.9)) was false, and §6.4's extent and reserve count rested on it:
  - (a) Near lw slots fill a band of width ≈ 101ℓ, so their weight is e^{cR₁}, which is unpayable. What closes it is not known. Keeping the band inside Ω₂ᶜ fails, since CRE (2.9) allows R₂ = R₁/L.
  - (b) Class-(I) slots depend on m̂ within R_dep ≍ log g₀⁻², so the reserve count is ~(log g₀⁻²)^d. Route: a walk expansion of m̂ plus interpolation into local pieces. The t > 0 species (O4) are affected too.
  §6.4 and §8 state both; the map D2.2(3) citation is removed from 6.4's label.
- S-B (the retreat-anchored step-1 masses put "inside the factor 2 per ℓ-cube" of 6.5): repaired. 7.1 has a new paragraph. Three step-1 masses are anchored at Ret(Λ) only: the att parts from D^{(0)}∖D(Λ) (IT-1 l.866–869), the E^∂ terms meeting D(Λ)ᶜ only in Ret(Λ), and the inputs term near Ret(Λ) only. Each is assigned to its nearest ℓ-cube of Ret(Λ). The per-cube bounds are Cρ̂₁c_CC_cM²R₁, 13^dm₁ and C_ing₀ϑ_VrM_VR₁; with §5's factor 2 their exponential is ≤ 2 per cube for small g₀. Together with 6.5's factor this gives 4^{#ℓ-cubes}, paid from Pol (s6 M9 above), with K₁ ≥ 8B + 12·2^dlog 2 in 6.5, 7.1 (twice) and §8. The later-step carry is part of O2′.
- m-a: repaired (m̄_{j+1} := sup_{n≥j+1}m_n in Res_merge and in 7.3's condition; X's n₁ extra steps are counted).
- m-b: repaired (C̄_A^{(j+1)} := sup_{n≥j+1}C_A(n); no class-(III) term, which is C_A(1)'s only).
- m-c: repaired (p.386 and (1.88) cited; p.385's condition is in p₀²).
- m-d: repaired (κ̂_{j+1} satisfies the enlarged (1.80); the costs are paid by 7.3's separate ¼p₀(g_j)).
- m-e: repaired (cube side M_VR_j and decay length M separated; the count is c_CM_VR_j#cubes·C_cM(1 + M/(M_VR_j))^d, a constant times M_VMR_j since both are constants).
- m-f: repaired in the map. (5)(f)'s small-domain ½(log)^{p₀} is marked superseded by 7.3's ¼p₀(g_j). The A_j lw term points to 7.1's weighted total with the label factor, class (III) and h(m̂_b) at 6.3's complex sup. *What is left* now points to closure §8.
- m-g: repaired (c_LF removed; it was unused).
- m-h: kept as given. 7.4(a)'s "same activity on ℓ and on ℓ₀" rests on D2.4(4) *Scope* and D2.3, which are not supplied, and 7.4(a) says so.
- Also fixed: 7.1's inputs bullet used the round-22 sup 4C_mC_μϑ_Vr. It is now 6.3's C_m^ℂϑ_Vr, in the sup and in C_in.

## Map, SW closure and §8 pass (03:39, 25 Oct, date)

Map (WILSON_IT1_D2_STEP_MAP_2026_10_22.md), Edit only:
- η_w := (5/16)η_V at l.170, l.270, l.336, (12)(b) *Base* (the ledger with V3's 1/16 and the complex 1/8, the tail split 𝔰³e^{(1/16+1/8+2+1+1/2)η𝔰}, Σ_tw_t's factor (62/5)⁴, and the note that the old 18/8 left out §3j(6)'s 2), (13)(a) and (14)(h) (s6 M14).
- D2.2(6)(e) *The radii*: r_{ω,j} := g_j^{1/2}, with the membership line and *Propagation* at the new radius (s2 n-1).
- D(k)(iii) and D2.2(6)(e): the slot convention at j = 0 (s6 S-B).
- D2.1(4) *Constants*: ε_H ≤ 2C₁a₁; the shrunk ε_H applies everywhere (s4 m-3, m-5).
- D(k)(ii)'s wrap display and (5)(g): max(C_S′ρ̂_j, C_S″b_j) (s2 n-8).
- D2.0(5) *The couplings* and *Result*: the D2.6 closure §5.0 uses the coupling upper bound through Cor. 8.2 (s5 m-4).
- (ii′-c): rewritten to closure 7.1's weighted total on every labelled term, with O2′ and O5 (s6, s2 n-16). D2.2(6)(c), (f), D2.3(9)'s "not reviewed" / "round 22 pending" tags updated (n-16).
- (5)(f): m-f above.

SW closure §1: (a1)(ii) is the component-and-traversal test (s2 S-2); the closing sentence "the complement of the attached species, exactly" is withdrawn, and the scope is the groups satisfying (i)–(iii) (s2 m-k, n-7). The closure's 2.1(a) label and §5.0 now cite this, not an "extension".

Closure §8: R-fr and R-src (real data) moved to *Accepted from Bałaban*, with their sources; the ω-radius, the j = 0 slot form and ε_H ≤ 2C₁a₁ added to the review list; the false condition 2R_dep < LM removed (part of O5); round 23 added to *Reviewed*.

## O5 repair (04:08, 25 Oct, date; at the user's "YEs")

Closure §6.4 *Extent and reserve count* rewritten (sources checked: V3 L3968, Lemma c4-8-2(c) and (c4-8-3) at L4768–4790; CRE (2.9) p.256 corrected transcription; IT-1 §3i(4), §3j(1)–(2)).
- (b) Class-(I) slots are expanded by interpolation in the box amplitudes s_Δ of K_𝐔: Y_i = Σ_XY_{i,X}, with X ∪ Start(i) connected, dependence set D_i(X) inside R_dep of i, σ ≤ 2^d(1 + N_adj + |X|), ext^B ≤ 2(|X| + N_adj + 1), and ‖Y_{i,X}‖ ≤ Ȳ(R₀−1)^{−|X|} by Cauchy on the polydisc |s_Δ| ≤ R₀. R₀ := 1 + 2eN_adje^{2^d+1} is absolute because ν_r = η < 1/128000 (1000ηA_s < ϖ/8, ϖ ≤ 1/16). New for review: ℓ_s with e^{μ_Hℓ_s/4}R₀q_s^ℂ ≤ 1/2 (contains 6.3(b)'s), and LM ≥ 4ℓ_s + 4ρ_L (ℓ_s, ρ_L precede M₁, M in V3's order). W_I := 2C_ste^{(2^d+1)(N_adj+1)}, W_III := e^{2^dν_r} replace W_lw in 6.3.
- (a) lw lineage extent measured from B := the 102ℓ-neighbourhood of Λ₁ᶜ. B ⊆ Λ_nᶜ for n ≥ n_B (G1 at step n, nesting, CRE (2.9)); before n_B the touch/merge factor is c̄ without bridge gain; total ≤ C_lin·lw_1(Z), C_lin := 2(1+C_δc̄)^{n_B}. 7.2 reads 2 as C_lin at j = 1.
- Also edited: 5.3 pointer, 6.2 *Units*, 6.3 (b) and the lw_1 display, 6.4's (T0) count and carry sentence, 7.1's M paragraph, 7.2, §8 (derived, review list, conditions, OPEN entry, *Reviewed*); map (ii′-c).
- Not closed by this: O4 (the interpolation localises the t > 0 species' m̂-dependence but does not bound their continuation).
