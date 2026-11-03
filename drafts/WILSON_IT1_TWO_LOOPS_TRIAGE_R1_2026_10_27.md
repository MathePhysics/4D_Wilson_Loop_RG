# Two-Loop Uniform Bound: Triage of the First Review Round (27 October 2026)

Note: `WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md`. Reviewed at 237 lines, SHA256 beginning c64ed33f641e. Repaired at 271 lines, LF, SHA256 beginning 2104e4b08818 (15:23).

Reviews (headless `claude -p`, `verification\isolated_reviewer\run_app_review_cli.ps1`):
- `two-loops-a-20261027-r1`: the opening block and Sections (1)–(5). No fatal, two serious (S1, S2), eight minor (M1–M8).
- `two-loops-b-20261027-r1`: Sections (6)–(9). One fatal (F1), two serious (F2, F5), five minor (F6–F10).
- Both exited 0. Both disclosed exposure to AGENTS.md. A also saw a Bałaban stop-hook injection, which it ignored.

## Outcome

- The note's claim of a K-uniform bound on the pair is withdrawn. F1 holds: the large-field factor B̄ had no source uniform over the labelled terms.
- The title and the status line now say what is derived: the exact identity (8.1), and a K-uniform bound on everything except the large-field cross words of the steps below the stopping step ((8.2)).
- Those cross words are the new open item (LF×), at the top of the note. What closes it is not known.

## Dispositions, Review A

- **S1 (long groups in (4)–(5)).** Holds. Repaired: (L×) is now stated for short arcs only; the last bullet of (4) says long groups are not covered. (5) cancels only clusters with no long group, and bounds the rest by (T′) at network diameter ≥ ℓ_iL^{K′−k}. This adds a term 8C_S′𝔞Σ_iℓ_iL^{K′−k}e^{−c_dℓ_iL^{K′−k}}, which is K-summable but does not decay in D. (7)'s C^×_E carries it as its third term, and (9) says so.
- **S2 (scope of (2C)).** Holds. Repaired: (2C) now lists (i) multi-interval arc sets, (ii) long-group connectivity and mass, (iii) the per-loop linked hull, (iv) base points, (v) the pair gas's KP condition, S° ≠ 0, and (T′), and (vi) r₀. It cites pins (a)–(d) as the step-1 model.
- **M1 (step-1 bound in (5)).** Holds. Repaired: the first step is now V4's E^×_Λ of lem:two-loop-retreated(a), with rate c_×/(LM) and ρ_V ≤ C(1+β₀)⁶ρ₁. C^×_E has a separate first-step term.
- **M2 (step-1 rate in (1)).** Holds. Repaired in (1).
- **M3 (r₀).** Holds. Repaired: r₀ is the step-k range, 2L fine units at step 1 (V4 L3696), a constant fixed before the coupling under (2C)(vi).
- **M4 ("linked through two things only").** Holds. Repaired in "What That Forces".
- **M5 (D2.1 product rule, modulus ≤ 1).** Holds. Repaired in (3).
- **M6 (norm bound at complex backgrounds).** Holds. Repaired in (1).
- **M7 (citations and labels).** Holds. Repaired: network at map l.1144; heading of (1); D2.0(1)'s contour bullet; step-1 base at D(Λ) via lem:two-loop-retreated proof (i); the opening names lem:two-loop-retreated.
- **M8 (C_S′ for the pair gas).** Holds. Repaired in (2C)(v).

## Dispositions, Review B

- **F1 (B̄ not uniform in k and K).** Holds, fatal. Not repairable in this round. The ℓ₀ / large-field split of (6) separates 𝔇^{LF}_{k+1}; its bound is (LF×). The B_pay / B̄ paragraph is deleted. Taking the supremum over labelled terms doesn't work (class-(III) slot costs of order one per fine slot, up to 4(ℓ₁+ℓ₂)L^{K′} slots). The weighted route would need a relative weight of the kind of the continuum note's (Q) at every step.
- **F2 (cross mass on ℓ ≠ ℓ₀).** Holds. On ℓ₀ repaired: deviation groups by (S-w), wrap groups at amplitude 𝔟̄ (map l.294), and (H×) in 𝔟̄. On ℓ ≠ ℓ₀ (collar groups, groups failing only (iv), merged groups with inherited attached members) it is part of (LF×).
- **F5 (R-steps).** Holds. Repaired: the split is made before the step's R-operation, which preserves the class part's integral (D2.7 closure note item 3); κ^{pre}_{k+1}; the κ-ratio uses C_κ := 8C_S′ + (8+4L)C_R and C′_ζ := C_ζ + C_R; the bounds on μ^R, ζ^R (map l.1146, D2.7 note 15.4) are listed as inherited. The continuum note's (6.1) has the same citation gap; that is recorded in the note's inherited line, not repaired there.
- **F6 (step-1 constants).** Holds. Repaired: C(1+β₀)⁶ in C_X and in C^×_E's first term.
- **F7 (notation).** Holds. Repaired: Λ uses the cumulative Σ_{j≤k+1}E^∂_j; C_ν includes C_χ; the wrap amplitude is max(C_S′ρ̂, C_S″b). The pl exponent keeps R-m's q₀, q₁, with a sentence in (1) separating them from the loops' q₁, q₂.
- **F8 (positivity inside T).** Holds. Repaired: e^{A} ≥ 0 at the real fields inside T is stated.
- **F9 ((8.2) comparison with (6.3)).** Holds. Repaired.
- **F10 (smallness of R^×).** Holds. Repaired: R^×_0 → 0 in the limit in which (H×) is imposed.

## Checks Made in the Repair

- The one-step bound on ℓ₀ was redone: under (H×), X ≤ 1/(2eD), the other factors ≤ 2L^me^{ν_×L^m/(2M)}, and D − 1/2 ≥ D/2 give the constant 16.
- The sum lemma's numbers were rechecked: the lacunary parts are 0.715 (p = 1) and 1.397 (p = 2), so the bound 3 holds.
- 𝔟̄'s size: ρ_k, ρ_{ph,k}, ρ_{t,k} (map l.295) and b_k ≤ Cρ_{t,k+1} (D2.6 closure §2.1) are O(g_k(1+2r_k)⁴), so 𝔟̄L^{q̄(j)} → 0 as γ → 0 with γ/g_min bounded.

## Next (as of 15:23)

- A second review round of the repaired note (both halves), if wanted.
- (LF×) has no known route. It is not a step a review can close.

## Closing the Open Items (15:56)

Note rewritten: 283 lines, LF, SHA256 beginning 25e1f6cdcb10. The title and status line now claim the K-uniform bound (8.2), except at the R-steps k+1 > N, which are the one open item, (2C-R).

- **(LF×), closed by a change of route.**
  - Cross groups are no longer taken out at the step that makes them. They are a species, cross(j), last in D2.0(3)'s order, carried uncontracted in the class to the stopping step.
  - The carry is the D2.6 closure §5 at lineage extent zero, without (T1) and (T3). Each step multiplies the mass by at most 1 + C_δc̄, as in 5.6's steps without a bridge.
  - Production by (S-w) on every labelled term, with extent ≥ δ_n/M, gives A^cr_{k+1} ≤ 4C_cr𝔞̄(ℓ₁+ℓ₂)L^me^{−ν_×DL^m/M}. Under (H^cr): C_δc̄ ≤ 1, the growth 2^m ≤ L^m is absorbed, and the sum lemma at p = 2 gives A^cr, uniform in K.
  - The large-field terms are then paid only at K′, by B^×_LF, with the factor e^{A^cr}. So F1's problem, a large-field bound at every intermediate step, no longer arises.
  - Removed with the old route: the split into N^{cr}, κ^{pre}, C_κ, C′_ζ, (H×), 𝔇^0/𝔇^{LF}, R^×_0, and R^×_{LF}. F2's remainder (cross mass on ℓ ≠ ℓ₀) falls away: attached cross groups are attached insertions, paid as for one loop, and the cross(j) mass bound holds on every labelled term. F5's split before the R-operation is no longer needed. Only the integral identity of D2.7 item 3 remains, and it is in (2C-R).
- **(2C), closed except at the R-steps, as the new section (6A).**
  - (i) Multi-interval arc sets: at most two intervals per vertex (+80 per window); carried insertions get windows per interval, with diam measured per class. That gives |win| ≤ 161Mσ and 242Mσ positions in place of 163Mσ.
  - (ii) Long groups and (iii) the linked hull: the covering lemma is used per loop.
  - (iv) Base points per loop, with the order C₁ then C₂.
  - (v) The Kotecký–Preiss condition with doubled per-position counts.
  - (vi) r₀ := 2 step-k units: map l.177 at step 1, and map l.478 with D2.3(4) (l.1083–1084) at k ≥ 1.
  - D2.2, D2.5, D2.6, and B^×_LF hold per loop or per component. D2.7 is the identity at k+1 ≤ N (item 1).
- **(2C-R), open.** At the R-steps, D2.7 15.1's Schur argument gives no scalar for the groups with slots on both loops, or for the groups whose arc words contain a cross insertion. With c_g := 0, D_g is the whole contraction, and 15.6(a), vanishing at pure gauge, fails. The bound from 15.4's activity bound and the span (≥ DL^{K′−k}/(MR_k) cubes), the cross part of E_k^R(C), item 3 for the pair, and the carry of these D_g are not written out.
- **Checked against the sources in this repair:** the D2.6 closure §5.0–5.6 (l.86–98); map l.177, l.280–286, l.478, l.1295, l.1526, l.1543–1547; D2.7 note items 15.1, 15.4, 15.6 (l.139, l.149, l.157–165) and the status list (l.200–211).
- **Not checked:** that the 41/M in map (12)(d)'s c_sh comes from the window alone. The note claims only that the second window term at most doubles c_sh's window terms.

## Next

- A second review round of the rewritten note: (6), (6A), (7), and (8.2).
- (2C-R): re-run D2.7 item 3 and items 15.1–15.7 for the pair.

## Re-Running D2.7 for the Pair (16:08)

Note: 316 lines, LF, SHA256 beginning 547ccd1cad85. New section (6B). (2C-R) is narrowed to the carry of the R-steps' small-field cross remainders.

- **Derived in (6B).**
  - Item 3: R′ preserves the integral of any integrable integrand; the gauge-fixing steps need only the invariance of the pair's word, which holds because every insertion is covariant at the ends of each interval of its arc set.
  - 15.0, 15.2, and 15.3 as identities: arcs on one or both loops; covariance per arc; 15.3's decomposition does not use the observable.
  - 15.5: per bond and per insertion. The attachment cost a_k at most doubles (eight straight sides in place of four), so 15.3's amplitude stays ≤ e^{−p₀(g_k)/2}.
  - 15.4's groups: interleaving is along one loop, so a group with slots on both loops contains a polymer whose slots lie on both.
  - 15.1 per loop. For the cross groups of the R-gas Schur gives no scalar, so c_g := 0, as for second-class components.
  - The cross constant E^{R×}_k by inclusion–exclusion of the four gases. Clusters meeting one loop only cancel; the rest have tree length ≥ DL^m/(MR_k) − 2, and (1.97) gives |E^{R×}_k| ≤ C^R(ℓ₁+ℓ₂)L^me^{−p₀(g_k)/2}e^{−βκDL^m/(MR_k)}.
  - The sum over the R-steps: with R_k < Lx^r and the minimum of ax^u + bx^{−v}, each term is ≤ e^{−c_R(DL^m)^θ}, θ = p₀/(p₀+r). C^{R×}_E is K-uniform, coupling-free, and decays in D. It enters E*.
  - 15.6–15.7 per loop for one-loop groups.
  - Cross R-remainders D_g^×: att when 15.6(e) applies; otherwise species cross(k), with production ≤ C^Re^{−c_R(DL^m)^θ} per traversal, summable with the L^m growth of (6).
  - 15.8: carried cross insertions outside class components are unchanged; inside, they make the group a cross group of the R-gas.
  - (9) gains the bound C^{R×}_E ≤ e^{−p₀(ḡ_R)/4}·(series at A₀/4), small when the couplings of the R-steps are.
- **(2C-R), narrowed and still open.** The small-field D_g^× are fixed members of (T0), so they need a reserve weight e^{aσ} with σ counted in π_k-cubes. Their bound decays only in the tree length in MR_k-units and in the scaled lengths of the attached insertions, while hull(g)⁺ has up to 3^dR_k^d π_k-cubes per MR_k-cube. The candidate payment is the part of Bałaban's volume factor in (1.95) that (1.96) does not use (LFR II p.389), which pays a rate a ≤ βκ/(12·2^d) on the polymer domains. The one-layer widening of hull(g)⁺ and the attached insertions' domains are not counted.
- **Checked against the sources:** the D2.7 closure note's item 3 (l.34–41), item 9 (l.109, l.111), and item 15 (l.135–167); LFR II p.389 (transcription l.19–46).
- **Not checked:** the other items of the D2.6 closure 5.5's reserve budget at a rate a of order Mε*.

## Next (16:08)

- (2C-R): the count of hull(g)⁺ in π_k-cubes against the unused volume factor, then the widening and the attached insertions.
- A second review round of (6), (6A), (6B), (7), and (8.2).

## (2C-R) Closed (17:37)

Note: 366 lines, LF, SHA256 beginning 87ac6d7aa8cd. (2C-R) is removed from the status line and from (9). The status line now names three conditions on constants: (H^cr), (H^R), and δM ≥ 2^{d+5}ν_r.

- **Unit correction.** d_k is in M-units ((1.67), p.376 l.29), not MR_k-units. The c_R, θ optimisation of 16:08 is replaced by the free decay c_F := min(1, δM/2, (κ₁−1)/4) per unit of the polymer length D_P: δ/2 per bond from 15.5 run at δ/2, and the half of e^{−(κ₁−1)} per cube that the resummation over Y′ leaves.
- **Derived in (6B).**
  - The volume: (1.95)'s factor is βκ/(6·2^d) per π_k-cube of X′_r, and (1.96) uses e^{−p₀(g_k)/2}100^dR_k^{−d} of it. The rest, a_V ≥ βκ/(12·2^d) ≥ ½, is unused. X⁺ is paid by the first-class components: #π_k(X⁺) ≤ ((102 + 2w_∼)R_k)^d, so 2ν_r#π_k(X⁺) ≤ p₀/16 by 2κ(100R_k)^d < p₀/2.
  - No widening: hull(g)⁺ is not used. The arc set ℐ(g) is the union of the slots' bonds, and |Ψ_g| ≤ C_Ψe^{−p₀(g_k)/2}#π_k(hull g).
  - The count σ_g, with #π_k(hull g) ≤ σ_g by the contour walk of each tree.
  - The payment at the rate 2ν_r: the cubes of X′_r from a_V/2, and the 2^{d+2}D_P cubes of the trees from c_F/2 under 2^{d+4}ν_r ≤ c_F.
  - The span rule of 15.4 for the pair: spans only for polymers with slots on one loop and no carried cross insertion. The other polymers are contracted on their slots' bonds.
  - The cross constant C^{R×}_E and the R-made mass A^{cr,R}, both with the factor e^{−p₀(ḡ_R)/2}, and with the decay e^{−c_FD/(2M)} and e^{−c_FD/(4M)} respectively.
  - The attached insertions: a group whose members include a carried cross insertion multiplies that member's weight by 1 + y^R_k, y^R_k := C_ye^{−p₀(g_k)/4}, with (T0)'s hard core and product form. (H^R) gives Π_k(1 + y^R_k) ≤ 2.
  - (7)'s carried total becomes A^× := 2(A^cr + A^{cr,R}), and (8.2) uses A^×.
- **Readings this rests on.**
  - R-far″ read on 𝐃_k, with Y′₀ ⊇ Y_W for the cross slots.
  - X^∼ ⊆ X′ (p.389 l.9–10).
  - w_∼ = 6 layers, from the continuum note l.92, which states it in K′'s convention.
  - κ₁ − 1 ≥ 2^{d+6}ν_r, inferred from the convergence of the resummation with ½(κ₁−1) per cube (p.376 l.37–39), not quoted.
- **New and unreviewed:** the span rule for the pair, and the split into the first case (D_g^× is a new insertion of species cross(k)) and the second case (the factor 1 + y^R_k).
- **Checked against the sources:** LFR II p.376, p.389, and p.390; PRT2 p.231 ((2.46)); the D2.7 closure l.135–169; the D2.6 closure l.84–97; the continuum note l.92.
- **Not checked:** map (12)(e)'s 81Mσ positions for R-made insertions, used through (6A)(i). The Kotecký–Preiss constants C_gr, C″, and C_KP are stated, not computed.

## Next (17:37)

- A second review round of (6), (6A), (6B), (7), and (8.2).

## The Four Readings Checked Against the Print (18:18)

Note: 369 lines, LF, SHA256 beginning 91d7266a34e3. None of the four readings of 17:37 remains a reading.
- **Pieces on 𝐃_k: quoted.** 𝐃_k is the class of connected unions of π_k-cubes of side M (RG I p.257 l.7–11). Y_1 is the smallest domain of 𝐃_k containing the term's domain (LFR II p.373 l.15), and each component of Y_2′, Y_3′, and Y_4′ belongs to 𝐃_k (p.373 l.33, p.374 l.10, p.374 l.28). The D2.7 closure's 15.5(ii)(β) writes Y′ as a connected union of MR_k-cubes; the print has 𝐃_k, and the two-loop note follows the print.
- **Y′₀ ⊇ Y_W: a definition.** Y′₀ is the cubes of the slot's bonds, its components, and its tree (D2.7 15.5(ii)); a cross slot's bonds are those of Y_W.
- **X^∼ ⊆ X′: dropped.** p.389 l.9–10 says only that X′ can be one of the X_j^∼. The note now uses X ⊆ X′_r, which is printed (X′_0 = ∪Y ∪ ∪X_j, p.387 l.42; components, p.388 l.2–3). X⁺ is X plus two layers of MR_k-cubes, so D_P's constant per X′_r is 4R_k + 2 in place of 2R_k + 2. The polylog absorption and the traversal count are unchanged.
- **w_∼ = 1: quoted.** ∼ means "adding one layer of cubes" of the family that defines the set (CRE p.245 l.40–43). The six layers came from the D2.6 closure's d₀ = 6 via the continuum note l.90, not from Bałaban. #π_k(X⁺) ≤ (104R_k)^d, and 2ν_r#π_k(X⁺) ≤ p₀(g_k)/16 holds since 8(1.04)^dν_r ≤ κ.
- **κ₁ − 1 ≥ 2^{d+6}ν_r: derived.** LFR II's "(6.10) [I]" and "Sects. 6, 7 [I]" are RG II's Sects. 1–2 (CRE p.276 l.23–28 cites (I.6.34) and (I.6.41), which are RG II's (1.34) and (1.41)). RG II's κ₁ is "a sufficiently big positive number" (p.5 l.7–8), with ½(κ₁−1) ≥ 2Lκ (p.20 l.17). With κ ≥ 6·2^d/β and β ≤ 1 (LFR II p.389 l.12, p.376 l.5), κ₁ − 1 ≥ 24L·2^d.
- **Also fixed:** (1.95)'s volume factor lives on X′∖∪Y_i, the Y_i the second-class components. The note now says why X′_r misses them: P meets none, and X′ either contains a Y_i or misses all (p.389 l.27–28).
- **Still inherited:** R-far″ itself, the D2.7 closure's reading of Bałaban's localisation expansion at the loop's bond variables.
- **Still not checked:** map (12)(e)'s 81Mσ positions for R-made insertions; the Kotecký–Preiss constants C_gr, C″, and C_KP (stated, not computed).

## Next (18:18)

- A second review round of (6), (6A), (6B), (7), and (8.2).

## Second Review Round: Triage and Repairs (20:10)

Reviews: verification\isolated_reviewer\reviews\two-loops-{s6,s6a,s6b1,s6b2,s7,s82}-20261027-r2, headless `claude -p`, all exit 0. No fatal finding. Note after repairs: 480 lines, LF, SHA256 beginning 144e0ba93692. (6B)'s rooted-sum constant is renamed C_jn, apart from D2.6's C″ in (6).

**Open: (6B-br) Joins across single-loop members at the R-steps.** Found during the repair of s6b1 S2 and s6b2's count. D2.7 15.5(i) joins the domain X_D of a carried insertion in a slot to the polymer, and D_P does not count a crossing of X_D.
- What is missing: the first case's decay e^{−c_FDL^m/(4M)} when the join between the loops runs across X_D, and *The rooted sum*'s root entropy for a polymer with a span whose slots are spread across X_D.
- What closes it, two routes:
  - by species, with the extent weight e^{ν_e·ext_k} (map l.292) for dev, att(k, ·), and wrap (rate min(c_F/4, ν_e/2)), plus a per-loop distance factor in the att(j, Z′) register (an amendment of map l.302);
  - by a half count of single-loop members in σ_g, which doubles (T0)'s units and moves L₀^× to 8·10⁴.
- (8.2)'s heading says it is open through (6B-br).

**s6 ((6)).**
- Serious 1, first-step production: repaired through lem:two-loop-pins(d) at D(Λ) (proof (v) of lem:two-loop-retreated), with the norm comparison written.
- Minors 2–8: §2.1(a)/(b)/(c) citations; pl_k; the pair-dependent C_V (also in (7)'s C^×_E); N_B for Bałaban's N and the animal constant renamed; the large-field wording, now also in *What That Forces*; the projective majorant; "(Derived Given …)" headings. All applied.

**s6a ((6A)).**
- Serious 1–2, window and shares: repaired by filled hulls, 170Mσ positions, and L₀^× = 4·10⁴.
- Minors: all applied (diam_v per interval, c_C, Cov(k) per interval, (T3), Γ-vertices, (12)(f)/(13)(b), B^×_LF, D2.7 items 2 and 12).

**s6b1 ((6B), first half).**
- S1, the (κ₁−1) budget: repaired. ½(κ₁−1) − κ ≥ (2L−1)κ ≥ 2 per cube; c_F := min(1, δM/2); the κ₁ chain is gone from *The payment*.
- S2, the evaluation of cross members in slots: repaired as 15.5(i)'s statement applied to W, inherited.
- m1–m7: applied (cancellation wording, 4R_k+4 and ℓ_a/M+3, X_D for every species, "bounded uniformly in K", the 𝐃_k amendment of 15.5(ii)(β), citations, the d_k budget, the (1.89) split, and (1.96)).

**s6b2 ((6B), second half).**
- Serious, the window sum: repaired by *The count*'s filled-hull diameter, diam_∞(S_g) ≤ Mσ_g.
- Minors 1–12: applied. Minor 3 (torus): the span bound now uses N_s ≥ 2max(ℓ₁, ℓ₂), as V4's tori have (L1565). Map l.193's (TC) is a cluster condition, so it is not cited. Minor 12: β < 1 is derived from p.376 l.5–6, and the κ identification is cited (CRE (I.6.34), (I.6.41)).

**s7 ((7)).**
- Minor 1, E* omits the R-steps' remainders E°^R_k(C_i): repaired. C^{R°}_E := Ce^{−p₀(ḡ_R)/2}Σ_i[3/c + e^{−c}(1+6/c) + ℓ_ie^{−cN_s}(1+6/(cN_s))] is added to E*, from D2.7 15.4(ii) (closure l.153, checked). (2)'s E^×_const,k now names E°^R_j and E^{R×}_j.
- Minor 2, linearity: restated.
- The product range is Π_{N_B<k≤K′}.

**s82 ((8.2)).**
- 1: as s7's minor 1.
- 2: B^×_LF is defined in (6A) as the payment without the cross factors, with e^{E^×_const} and e^{E^∂} inside. The proof bullet cites that definition.
- 3–6: the heading names the inherited inputs and (6B-br); the hypotheses add L ≥ L₀^× and N_s ≥ 2max ℓ_i; the uniformity is stated through the coupling windows; P2's factorisation over lineages is explicit; the comparison list is completed.

**Inherited, reported, not edited.** The continuum note's (2), (5.2), and (6.3) omit E°^R_k(C) from E_const. Its (6.3) wrap amplitude is ρ̂_j, not map l.294's amended one. The first is recorded in the two-loop note's header, and the second in (8.2)'s comparison list.

**Not checked.** The Kotecký–Preiss constants C_gr, C″, and C_KP are stated, not computed.

## Next (20:10)

- The user's choice of route for (6B-br), then its repair and a review of (6B).

## (6B-br) Closed by the Half Count (20:32)

The user chose the half count. (6B-br), the joins across single-loop members at the R-steps, is closed in the note. Nothing in the note is open beyond its inherited inputs. Note SHA-256 after the repair: ee6eec4e22c7d42042997b2e421b34f0d9dbe01eb4798aa99c90afadc66f4497 (484 lines, LF).

**The route.** σ_g counts a single-loop member at σ(D)/2. The other half of the member's D(k) weight e^{ν_rσ(D)} pays its joins, its share of the root entropy, and the first case's crossing decay. The budget per single-loop member is λ_k/2 + ε_k/2 (D_g^×'s weight and the Ψ part), ε_k/4 (joins), 1/8 (root entropy), and 1/8 (first case), in units of ν_rσ(D), with total ≤ 1/2 + 3ε_k/4 + 1/4 < 1 for ε_k ≤ 1/32. It covers every species uniformly, att(j, ·) included, so the map's att register is unchanged.

**Changes in the note.**
- (6B) *The count*: the half count; cross insertions have units with factor 4 (#_k + n_k/M ≤ 4σ, diam_∞(X_W ∪ ℐ(W)) ≤ 4Mσ), by induction on the production step; diam_∞(S_g) ≤ 4Mσ_g uses diam_∞(span P) ≤ diam_∞(dom P).
- (6B) *The payment*: the member Ψ part is 4C_Ψ′Me^{−p₀(g_k)/2}Σσ(D); the single-loop member budget above.
- (6B) *The rooted sum*: members carry e^{−(ε_k/4)ν_rσ(D)}, single-loop ones also e^{−(ν_r/8)σ(D)}. The span lemma is proved: on a square of side s, a set of ℓ^∞-diameter δ < s lies on one side or on two adjacent sides within δ of their corner, so its span has ≤ 2δ bonds and diameter ≤ δ; for δ ≥ s the loop has ≤ 4δ bonds and diameter ≤ δ. The root entropy of a joining polymer with members is (4M(D + S) + 1)e^{−(c_F/8)D}e^{−(ν_r/8)S} ≤ 1 + 32M/(ec_F) + 32M/(eν_r), so C_jn and C_gr now depend on ν_r. A member's join factor is (1 + C_jne^{−p₀/2})^{8Mσ(D)} ≤ e^{(ε_k/4)ν_rσ(D)}.
- (6B) *First case*: one argument for all first-case groups. With D_P + Σσ(D) ≥ DL^m/M and c_F/4 ≥ ν_r/8, the decay is e^{−ν_rDL^m/(8M)}, and A^R_k ≤ 4e^{c_W}C_gr(ℓ₁+ℓ₂)L^me^{−p₀(g_k)/2}e^{−ν_rDL^m/(8M)}. The conditional sentence is removed.
- (6B) *Second case*: ≤ 4σ(W) cubes of X_W, and C_y := 16C_gr/(eν_r).
- (6B) *The R-made total*: a := ν_rD/(8M), A^{cr,R} := 4e^{c_W}C_gr(ℓ₁+ℓ₂)e^{−p₀(ḡ_R)/2}e^{−ν_rD/(8M)}(1 + 768M²/(ν_rD)²).
- (6A)(i) *Units with a factor*: positions 170cMσ; window sum C_win^× ≤ 196c/c_w; the share for c(8496ν_f + 88ν_e)/L ≤ ν_r/4. At c = 4: (T0)'s condition is (680 + 784/c_w)M(ε^{new}_{re-run} + ε^{old}_n + ε^{ref,n}) ≤ ν_r/8.
- Header and (8.2): L₀^× = 1.5·10⁵; "open through (6B-br)" removed from the (8.2) heading.

**Correction.** The estimate L₀^× = 8·10⁴ given to the user before the edits was wrong: the cross units carry the factor 4, so the share needs 4(8496·17/16 + 11)/L ≤ 0.242, that is L ≥ 1.5·10⁵.

**Not affected.** E^{R×}_k's bound (rate c_F/2): no carried insertion enters those gases (note l.338).

**Not checked.** The Kotecký–Preiss constants C_gr, C_jn, and C_KP are stated, not computed.

## Next (20:32)

- A headless review of (6A)(i) and (6B) against their sources.

## Third Review Round: Triage and Repairs (21:24)

Reviews: verification\isolated_reviewer\reviews\two-loops-{s6ai,s6bc,s6br}-20261027-r3, headless `claude -p`, on the note at SHA ee6eec4e22c7. No fatal finding. Two serious findings, both repaired; every minor applied. Note after repairs: 522 lines, LF, SHA-256 9adce3fcc846f445f7cdab09d9f89d64533e7e338c54725790735de6c2bc3db3.

**s6ai ((6A)(i)).**
- S1, serious, the per-loop diam_v of an M-vertex: map (12)(d)'s bound puts a point of a touched X_W within diam_W of W's interval, which can lie on the other loop. Repaired with Q_v := M ∪ ∪S_W ∪ ∪supp 𝒞, closed-connected (M connected, each touched X_W meets M by map l.676, S_W connected, each 𝒞 touches M), so diam_v ≤ M#(M) + Σ_W(diam(S_W) + 1) + Σ_𝒞(M#(𝒞) + 1). The reviewer's "second-stage" W does not occur: every W ∈ 𝔅(M) has X_W meeting M. Consequences recomputed:
  - the M-part of the window is unchanged, so (282ν_f, 441ν_e) and the cube cost 7.6 stand;
  - a touched single-interval W has |win(W)| ≤ 81c_W(M/L)σ_k + 80, sh(W) within (ν_r/4)σ_k + c_sh′ for L ≥ 5081c_W, c_sh′ ≤ c_sh^×; c_sh^× now replaces c_sh for every insertion (note l.68);
  - a touched multi-interval W stays within its own |win(D)| bound;
  - a vacuum link's window doubles, and sh(𝒞) ≤ (164.125ν_f + 85ν_e)#(𝒞) ≤ 2(83ν_f + 86ν_e)#(𝒞) ≤ #(𝒞)/4 stands.
- m2, the factor c_W of touched R-made insertions: 48c_W and 96c_W in the M-vertex counts; the passed part needs L ≥ 8832c_W, covered by L₀^×.
- m3, the induction: S_D closed-connected for every old D is now the stated hypothesis. Base at step 1: #_1(X_W) ≤ n(W) (V4 L5197), each hull interval holds a contact within 2L fine units of X(W) (proof of lem:two-loop-pins(b)), so cross(1) has c ≤ 1 + 4/M. The connectedness of V4's group domains at step 1 is the single loop's step-1 reading (map l.1551), now listed under *Inherited*.
- m4: C_win^× is shown to cover the other vertices' four-ended windows, 4(21 + 20/c_w) ≤ 164/c_w.
- m5: sh(M) restated, ν_f(282#(M) + 22) + ν_e(441#(M) + 164) + (3ν_f + 9ν_e)(96/L)Σc_Wσ_k(W) + …; the constant part ≤ 0.045 is charged to one component cube, within κ_s^{(12)}/4's constant 4.
- m6: the gap arc is to the nearest piece. The D2.2(4)(e) enlargement adds nothing for the pair: a cut piece would contain a bond of C in Y, and its owner's domain contains it (Cov(k), map l.622), so the owner is touched and the piece lies inside the arc.
- m7: *Units with a factor* names the closed-connectedness of S_D.

**s6bc ((6B), 15.6, *The count*, *The payment*).**
- A7, serious, |Ψ_g| missed the clusters joined through a span of a polymer of g: the term C_Ψ′e^{−p₀/2}Σ_{P with a span}|span(P)| is added. The polymer part now has 1 + 20M (2^{d+1} + ½ + 20M ≤ (1 + 20M)2^{d+2}); the member part 8C_Ψ′M, under 16C_Ψ′Mε_k ≤ ν_r.
- B3: B_P uses X⁺⁺ (X⁺ plus one π_k-layer), which holds Y′₀'s cubes at slot bonds on ∂X⁺; #π_k(X⁺⁺) ≤ (105R_k)^d, and 8(1.05)^dν_r ≤ κ.
- A5: D_g^×'s box is hull(g)⁺, for 15.6(e)'s scope rule.
- A2: a group's span is ∪_{P∈g}span(P), with the reviewer's example of D2.7 15.6's shortest arc holding a foreign slot.
- A3: the covariance of a slot holding a cross member is argued on the whole slot, by 15.2(α)–(β).
- F2: member weights cited species by species. wrap(j), j ≥ 2: (S-w) keeps e^{ν_rσ_j} through D2.6 closure 2.1(e)'s derivation, carried with growth L (map l.367). wrap(1): from IT-1 note §3a(4)(ii) and the pin e^{4η𝔰} (§3a(6); V4 lem:two-loop-pins(d)), Σ_{wrap(1)}e^{θ° + ν_r𝔰}‖Υ⁰_W‖ ≤ 2K_χCρe^{−(11/4)ηN_min/(CLM)}; only the constant of map (5)(g)'s torus condition changes. lw: D2.6 closure §6.4; att: D2.6 closure 5.0.
- D4: LFR II's δ (p.376) is read as CRE's decay rate δ of the 𝐇-bounds B₃exp(−δ·) (LFR II p.368 l.23; CRE p.250 l.47, p.251 l.39, p.268 l.41, same B₃), which CRE fixes before M₂R₁ is taken large (p.250 l.47–48). Listed under *Inherited*; the source of the operator bounds in PRT2 was not located.
- B2: the base case as under s6ai m3 (c ≤ 1 + 4/M ≤ 4), and the coarsening step shown (#_k ≤ #_j, n_k ≤ n_j, diameter 4Mσ/L + 2M ≤ 4Mσ).
- B4: l.299's reading is for Y′₀ and dom P only; ℐ(g) takes ℐ(D).
- A8: the att case's member pays its Ψ part and join count from its weight, factor ≤ w_{k−1}(W)e^{−(ε_k/4)ν_rσ(W)}.

**s6br ((6B), the rooted sum to 15.8).** No serious finding.
- m1: the root cost weights the offset j by e^{−cj}, c := min(c_F, ν_r)/(32M): ≤ 2^d(1 + 32M/min(c_F, ν_r)) per cube sum; C_jn := 2^{d+1}C_KP(1 + 32M/min(c_F, ν_r)).
- m2: joins at one position are a set: e^{C_jne^{−p₀/2}} per position; the polymer part needs 160MC_jne^{−p₀/2} ≤ c_F.
- m3: C_KP and the multiplicity 2^d are named.
- m4: "meeting b"; the cross-references of *Joins* and *First case* are explicit.
- m5: the convention for members' norms is stated in *The rooted sum*.
- m6: 15.8 has four classes; the cross insertions in a second-class block Y_i^∼ keep their factor in the cross product, as in 15.6(e)'s case, evaluated by item 7 as 15.5(i) is (extension of that inherited reading, listed).

**Noticed, outside the note.** D2.7 15.6's span, the shortest arc containing a group's slots, can hold a slot of another group (A2's example), while D2.7 states "the spans of distinct groups of 𝔉 are disjoint". The single-loop closure needs the same union definition. Not edited.

**Not checked.** The Kotecký–Preiss constants C_gr, C_jn, and C_KP are stated, not computed.

## Next (21:24)

- A re-review of the repaired parts of (6A)(i) and (6B).
- D2.7 15.6's span definition for one loop.

## D2.7's Group Span Repaired (21:55)

The defect: D2.7 grouped polymers when "a slot of P lies between two slots of P′" and took span(g) as the shortest arc containing all of g's slots. With slots at 0 and 40 for P₁ and at 30 and 75 for P₂ on a loop of 100 bonds, the shortest arc is 75 → 0 → 40, and a slot at 90 of a polymer interleaving neither lies in it. So D2.7's "the spans of distinct groups of 𝔉 are disjoint" failed, and with it the expansion of 15.6 over disjoint stretches of C. The covering sentence of 15.4 ("covered by its polymers' domains") was also wrong: the arc between two slots of a polymer need not lie in its domain, for example around a corner of C.

The repair, in WILSON_IT1_D27_CLOSURE_2026_10_26.md:

- 15.4 now defines span(P) per polymer (shortest arc containing P's slots, with a fixed tie-break), interleaving as "a slot of P meets span(P′) or conversely", the groups as the classes of the generated equivalence, and span(g) := ∪_{P∈g}span(P).
- 15.4 proves that two members with spans sharing a bond interleave (the walk along span(P′) to its end either stays in span(P) or leaves it through an end of span(P), a slot bond), so distinct groups have disjoint spans and no group's span meets another group's slot; span(g) is an arc with slot ends, or C.
- 15.4's covering sentence is replaced by a bound: C is the square of side s_k (map l.241) and the torus periods exceed 2s_k (map l.1159), so span(P) lies in (dom P)^{+|P|}, has at most 4|P|MR_k bonds, and meets at most 4|P| + 10 cubes; hull(g) meets at most 15Σ|P| cubes. The entropy of groups through a cube is paid by half of e^{−κ(size)}.
- 15.6 takes span(g) from 15.4, with ends a, b (a = b when span(g) = C), and cites 15.4 for the disjointness.
- 15.7's diameter bound is now diam_k(hull(g)⁺) ≤ MR_k(2 + 3n_g), which keeps diam·e^{−κ(size)} ≤ 100MR_k·Ce^{−κ(size)/2}.

The two-loops note now cites 15.4 for the union and drops its paragraph on the discrepancy.

## Next (21:55)

- The headless review (r4) of the repaired parts of (6A)(i) and (6B), and of D2.7 15.4 and 15.6's span repair.

## Fourth Review Round: Triage and Repairs (23:31)

Reviews: verification\isolated_reviewer\reviews\two-loops-{s6ai,s6bc,s6br}-20261027-r4 and it1-d27-span-20261027-r1, headless `claude -p`. No fatal finding. Every serious finding is repaired or filed as OPEN in the note's header; every minor finding is applied. Note after repairs: 580 lines, LF, SHA-256 9bf941a6524d9968b5e6da550507b8b227ed7109fc321fe2ba2559e1895173ba. D2.7: LF, SHA-256 b5dd8a5dbceba17406788036357761803a77c847db1139e0624f74bfbd576a6a.

**Open after this round (header blocks of the note).**
- OPEN (R-eval): the bound of the carried insertions at the R-step's evaluation points, the large-field old variables included. D(k)'s masses are sup bounds on 𝒟^{sub}_k, D2.7 item 5(b) (l.54) records the uniform analyticity as not supplied, and the D2.6 closure 5.1 covers the T-steps only. It enters at 15.5 for the cross members and at 15.8's third class.
- OPEN (R-att): the polymer part of the weight of the cross groups of the R-gas whose polymers meet a second-class or unchanged component (15.6(e)'s second alternative). *The free decay* and *The volume* hold away from those components only. What closes it: a bound by the component's reserve Res(Z), through #π_k(X′) ≤ 2^{d+1}(d_k(X′) + 1); the comparison of d_k with d′(Z) and the sum over the polymers charged to Z remain.

**it1-d27-span-r1 (D2.7 15.4–15.7).**
- S1, serious, what stands on span(g)'s bonds outside the slots: 15.6 takes as the members 𝒲_g the insertions of the term at U^R whose intervals share a bond with span(g). Each lies in span(g), since its interval holds no slot bond and the ends of span(g) are slot bonds; the groups with members are 15.6(f)'s.
- m1–m12 applied: the covering case in the definition, the tie-break and the fact that ties need t ≥ s_k, "shares a bond with", s_k at map l.241 and l.1087, N^{(k)}_min ≥ 2s_k as the quantified part of l.1159's "≫", the pieces in dom P, |P|(2|P|+1)^d positions per shape, size(P) defined, the three-way split of e^{−κ(size)}, the end site when span(g) = C, n_g := Σ|P| with 15.7's chain argument.

**s6ai ((6A)(i)).**
- Serious, the base and the meaning of X_W: the step-1 S_W is the closed 8M-neighbourhood of X(W) ∪ ℐ(W), closed-connected by V4 lem:two-loop-pins(a) *Connectivity* (2L ≤ 8M), and it carries the Cov domain; #(X_D) stays for the counts. ℐ(W) has at most 2n(W) intervals, so u₁ = 1 + 4/M + 48/L.
- Minors applied: the R-made hypothesis through S_g (now with the members' T_D); the term-by-term window comparison; c_W and the vacuum constant separated; the nearest-piece rule stated as the definition; the step-1 factor in place of "c = 1"; the interval count used at step 1 only; the vacuum-link clusters in the connectivity list; 80c_π, 84c_π, ℓ_X's 320, and the arc choices named; the (T0) smallness in the header; the line number.

**s6bc ((6B), 15.5–15.6, *The count*, *The payment*).**
- C3, serious, the slot of a cross member: a single (arc piece)·W·(arc piece) does not serve when W has intervals in several X⁺. The slot now contracts W with all the arc pieces of the arcs of C ∩ ∪_{X∈P}X⁺ that contain its intervals, and W's intervals outside every X⁺ stay open (*The slots of a cross member*). Each interval of W inside a first-class X′⁺ lies in a component of P, since Y′₀ ⊇ X_W forces the polymers to overlap. The slot is invariant at the fixed sites and covariant at the arc ends and the open ends, so 15.2(α)–(β) apply to T_P.
- C8, serious, 15.6(e)'s scope rule. The reviewer's claim that *The payment* does not depend on it is wrong for the polymers that meet a second-class component: *Lengths*, *The free decay*, and *The volume* assume none. Repaired as follows:
  - the first alternative (collar) is SW §1(a3)'s rule for dev terms and does not apply to D_g^×;
  - the second makes the group att(k, ·), charged to the component as for one loop;
  - with a cross member, D_g^× is in the first cross member's lineage and stays in M^cr (an att-first lineage would count the cross members' σ twice);
  - without one, it is att(k, ·) in the D2.6 closure §5;
  - *The payment*'s polymer part is restricted to the other groups, and the rest is OPEN (R-att).
- Design change in *The count*. A single-loop member's step-k units, at weight 1, failed by the rounding and by the double count in the spans. The note now uses the production σ of every member (map l.1531), the one its weight carries, and keeps the single-loop weight ½. Each member has a closed-connected T_D containing X_D ∪ X^{Cov}_D ∪ ℐ(D): S_D when made at step k, and its step-k domain otherwise, of diameter ≤ M#_k(X_D). This gives counts ≤ (21/20)σ and diameter ≤ (21/20)Mσ for the single-loop members, and 6σ, 6Mσ for the cross ones. D2.7's single-loop R-made insertions get (H0)–(H2) with u = 1: counted domain the π_j-cubes meeting hull(g) and the members' domains, with multiplicity, and S := (those cubes) ∪ ∪T_W. D_g^× then has 6σ_g, 6Mσ_g, X_{D_g^×} := hull(g), and S_{D_g^×} := S_g.
- m1: a slot's arc set is its tensor's bonds, its arcs of C ∩ ∪X⁺, and its carried insertions' intervals outside every X⁺.
- m2: e^{3c_F} per attached insertion replaces a_k(X) by e^{3c_F}a_k(X) ≤ e³a_k(X); 15.3's amplitude stands for small g_k.
- m3: "is at most"; the member part of |Ψ_g| is now ≤ 6C_Ψ′Me^{−p₀/2}Σσ, under 12C_Ψ′Mε_k ≤ ν_r.
- m4: resolved by the production σ; no comparison σ_k ≤ σ_j is used, so the factors 1 + 2/M and 1 + 1/M do not arise.
- m5: wrap(1) books §3j(6)'s 2η𝔰 on the same pin (map l.1532), so the rate is (3/4)η/C; l.1532 is cited for e^{η𝔰/8}, and (7)'s c_w is at most this rate at j = 1.
- m6: keeping e^{ν_rσ_j} on wrap(j ≥ 2) is labelled an amendment of the D2.6 closure 2.1(e), derived in the note.
- m7: X_{D_g^×} and S_{D_g^×} are named; the units hold through S_g.
- m8: CRE p.251 l.39–40 (below (1.21)) is cited for δ before M; map l.973's δ₀ is VAR's rate and is dropped from the clause.
- m9: no change; "< p₀/2" is what is used.

**s6br (*The rooted sum* to 15.8).**
- Serious, 15.8's third class and the cross members on the R-step's integration domains: the reading was disclosed but filed as inherited. It is now OPEN (R-eval), at 15.5, in *The rooted sum*, and in 15.8. Class 3 cites D2.7 item 5(a)–(b) (l.54, l.58, l.60), with the e³ loss at complex data kept in 5(b)'s mass.
- m1: C_gr := 2^dC_KP·C_B, C_B the constant factors of B(g) (its 2, D(k)(iii)'s e^{A_k} for each loop's words, dim V_{π₁}·dim V_{π₂}); the dependence list names χ₁, χ₂ and the A_k bound.
- m2: the l.139 citation is replaced by item 5(a)–(b).
- m3: "item 7's evaluation of the slot insertions" is removed.
- m4: the 1/m! is from summing over sets.
- m5: V4 L3560 is cited with L1565.
- m6: 15.8 states the precedence (slot classes before the block class); class 1 says "none of its intervals lies in an arc of C ∩ X⁺" and "untouched by R and re-evaluated at U^R"; the single-loop members' norms in e^{2ΣA} exclude the dev parts joined through a 𝒦 ≠ ∅; the convention persists for composites; the join rate is c_j.
- m7: the hard core states why a cross member with intervals in two first-class homes is in one polymer.

**Constants changed.** u = 6 for the R-made cross insertions (was 4); (T0)'s smallness (1020 + 1176/c_w)M(…) ≤ ν_r/8; L₀^× := 2.5·10⁵; segment cubes 29σ(W); c_j := min(c_F, ν_r)/(34M) and C_jn := 2^{d+1}C_KP(1 + 34M/min(c_F, ν_r)); the member join factor under 24MC_jnε_k ≤ ν_r; the first case's rate ν_rDL^m/(9M); C_y := 24C_gr/(eν_r); A^{cr,R} with e^{−ν_rD/(9M)}(1 + 972M²/(ν_rD)²).

**Noticed, not edited.**
- Map l.1551's step-1 factor omits the halo, an O(1/L) effect.
- D2.7's single-loop R-made insertions now have a counted domain that includes the π_j-cubes meeting hull(g). Their weights e^{ν_rσ} with this σ are paid neither in D2.7 15.7, whose sum spends e^{−κ(size)} on the diameter, the entropy, and the Kotecký–Preiss margin, nor in the note. For the att ones this is the single loop's part of OPEN (R-att); for the dev ones, map (ii-w) at the R-steps, (6B)'s *The payment* is the argument to be written in D2.7. Both are now named under OPEN (R-att), *Where it enters*.

**Not checked.** C_KP, C_B, and the A_k bound are stated, not computed.

## Next (23:31)

- OPEN (R-att): the reserve comparison of d_k with d′(Z), and the sum over the polymers charged to Z.
- OPEN (R-eval): a bound of the carried insertions on the R-step's integration domains.
- A re-review of *The count*, *The units of the members*, and 15.8.

## Closing the R-Step Gaps (28 October, 02:41)

Note: 625 lines, CRLF, SHA256 beginning 2bcf800b6516. D2.6 closure: 177 lines, 1d2d892687ad. D2.7 closure: 214 lines, 6cad5f724df9. All three notes, and the untouched continuum note and map, are CRLF on every line, and the edits kept that.

**Closed: (R-att).** New section (6C), *The attached groups*.
- The weights. A cross group with a cross member keeps e^{λ_kν_rσ_g}. The others carry the D2.6 closure 5.0 att weight, whose extent ext^{coll} ≤ 6σ + 2R_k + 1 costs (9/32)ν_rσ plus a polylog constant paid by the margin of (1.89). The polymer rate rises from 2ν_r to (5/2)ν_r, and a single-loop member's budget becomes 1/2 + 3ε_k/4 + 1/4 + 9/64 ≤ 1.
- First case (unchanged components only). (1.95)'s activity at X′ disjoint from ∪Y_i has c₁ = e^{−p₀} (p.390 l.2), the full decay, and the volume factor on all of X′, and (1.66)'s pieces' factor is over all of Y′. So *The free decay*, *The volume*, and *The payment* hold verbatim, under 5·2^{d+2}ν_r ≤ c_F and 10(1.05)^dν_r ≤ κ.
- Second case (second-class Y_i). #π_k(Y_i) ≤ (101R_k)^d (p.387 l.13); d_k ≤ d_{k,∪Y} + dΣ(#π_k(Y_i) + 1) by a tree argument; the cost per Y_i is ≤ (d + 1)(102R_k)^d; the roots move to the layer Y_i⁺∖Y_i. Each Y_i lies in at most one polymer (p.389 l.27–28), so the parts multiply to Π_iE(Y_i), E(Y_i) ≤ e^{p₀(g_k)/16} under 8(d + 1)(1.02)^d ≤ κ.
- Payment of E(Y_i): the D2.6 closure 7.2 small-domain branch is amended. κ_{j+1} takes (11/16)p₀(g_j) in place of ¾p₀(g_j), Res gains (3/16)p₀(g_j) in place of ¼p₀(g_j), Pol and κ̂ are unchanged, and p₀(g_j)/16 is free. *Use of Res*'s clause is now (3/16)p₀(g_j) ≥ 4m̄_{j+1}·13^d100^d(n₁ + R_{j+1} + 1), which holds for small g_*. 7.3's small-domain ledger is amended to match. When S(Y_i) is merged, either form of its number in (1.85)–(1.86) leaves the p₀(g_k)/16 free.
- The charge m^R at Y_i is ≤ O(1)e^{−(7/16)p₀(g_k)}, still ≤ m_k.
- The single loop's R-made groups whose slots hold no carried insertion: σ(D_g) ≤ Σ_P(#π_k(B_P) + 2^{d+2}D_P) + σ_𝒲, paid at (5/2)ν_r by *The payment* or by the two cases. D2.7's members 𝒲_g are the term's insertions in the gaps of span(g) (D2.7 l.157), carried by 15.6(f). The counted domain X_{D_g} now counts the cubes of H_g outside the members' domains, and *The units of the members* derives (H1) for this count.

**New OPEN (R-span).** A single-loop R-made group with a carried insertion D in a slot: span(g) can run across X_D, so σ(D_g) gains up to (21/5)σ(D) besides #_k(X_D) ≤ (21/20)σ(D), while D's weight gives e^{ν_rσ(D)} once. ℐ(g) in place of span(g) would lose 15.1's Schur scalar. It enters map (ii-w) and (6B)'s members.

**Partly closed: (R-eval).** (6C), *The evaluation points*. The integration variables of 𝐓′_k are real (p.379 l.29, l.37; p.378). By (1.65), the old configuration lies in Ũ_k″^c(Y_1, α̃), "contained in the analyticity domain" (p.375 l.29–30), and the insertions are functions of the same configuration. This gives D2.7 item 5(b)'s uniform analyticity, the slot bounds inside e^{2ΣA}, and 15.6(c)'s A_k. The 𝒟^{sub}_k small norms and the values at U^{𝒦} stay OPEN, restated with what closes them.

**Edits elsewhere in the note.** The stale "OPEN (R-att)" references (15.6(e)'s scope rule, *The payment*, *Second case*, 15.8) point to (6C); 15.5 and 15.8's third class say that (6C) places the R-step's points in 𝒟_k only; (8.2) names (R-eval) and (R-span); δM ≥ 5·2^{d+3}ν_r, 5·2^{d+2}ν_r ≤ 1, and (5/2)ν_r ≤ ¼ replace the old conditions in the header, (8.2), and the comparison list. Line citations of LFR II follow D2.7's convention, printed line = transcription file line + 1.

**D2.7 closure.** Item 5(b)'s "a D(k)(iii) property not supplied here" now points to the note's (6C), with the small norms named as OPEN (R-eval).

**Not checked.** No review has run on (6C), the D2.6 amendment, or the D2.7 pointer.

## Next (02:41)

- OPEN (R-eval): a 𝒟^{sub}_k version of (1.65), and its extension to U^{𝒦}.
- OPEN (R-span): a bound of the span gaps by a share of σ(D), or a form of D_g whose arc skips them and keeps 15.1's scalar.
- A review of (6C), with the D2.6 7.2–7.3 amendment and the D2.7 item 5(b) pointer.

## Closing (R-span) (28 October, 03:22)

**Reviews blocked.** The three headless reviews (att, single, eval) exited at launch with the CLI session limit, which resets at 04:20. App review sessions cannot be started while the user works over Remote Control. The relaunch is at 04:21.

**Routes that do not work.**
- A share of σ(D) does not cover the gaps: through diam(S_D), a two-interval D on opposite sides of the square has a gap of about 2σ(D).
- Taking the arc set ℐ(g) loses 15.1's scalar. The scalar is needed: the group's flat value is an integral of D over 𝐓′_k's variables, not 0, and a non-scalar flat part summed over the blocks of C is not bounded in K.

**Closed: (R-span).** (6C), *Groups with a carried insertion in a slot*.
- D_g carries e^{ν_rσ̃(D_g)}, with σ̃ := polymer part + ⅓Σ_Dσ(D) + σ_𝒲. Its units are those of (6A)(i)'s *Units with a factor* at u = 16, since 21/20 + 21/5 = 21/4 ≤ 16/3.
- The factor does not propagate. A carried D is made at j < k and has passed a T-step, where its descendant takes its own σ with u = 1 (l.426). So u_D ≤ 21/20, and the cross factor 6 stands.
- The gap arcs lie in the ℓ^∞-box of their end bonds, so D's part of the extent is ≤ (21/20)σ(D).
- D's budget: ⅓ + 3ε_k/4 + ¼ + 21/160 ≤ 1. With ½ in place of ⅓, it would be 1.03.
- Constants: L₀^× := 6·10⁵ (in place of 2.5·10⁵), and (T0)'s (2720 + 3136/c_w) (in place of 1020 + 1176/c_w). They are changed in the header, in (6A)(i), and in the factor lists (l.300, l.426).
- The header's OPEN (R-span) block, the title of (6C), and (8.2)'s exception now name (R-eval) only.

**Line endings.** The note, the closures, and this file are LF throughout (checked byte by byte at 03:20). The packets now say LF.

**Packets.** The note is now 625 lines, LF, SHA256 7bf67f139859…. The three packets carry the new hash and line ranges. The single packet's claim and Q4 cover the new paragraph and the changed constants.

## Next (03:22)

- 04:21: relaunch the three reviews. Triage each report as it lands.
- OPEN (R-eval): a 𝒟^{sub}_k version of (1.65), and its extension to U^{𝒦}.

## Working on (R-eval) (28 October, 03:31)

**Read.**
- LFR II p.374 (1.63): U_k^0 is the minimiser for block data drawn from 𝐔.
- LFR II p.375: values in the new determining set's space Ũ_k″^c, LFR I's (1.64)–(1.69) with n = N; the old set's conditions are weaker on the crucial domain.
- LFR I p.191: the spaces are defined by block-scale conditions with the constant BCM, B = B₃.
- VAR p.279, Theorem 1: |A| < B₃Mε₁(L^jη)^{−1}, with "a₀, a₁, B₃ depend on d and L only".
- D2.7 15.5(ii): U^{𝒦} is the same construction with old data on 𝒦, a minimiser, not a glued configuration.

**Routes that do not work.**
- *Direct inclusion of the sub-domains.* The R-step makes the layers more recent on the crucial domain (n_new ≥ n_old). The sub-domain factor 1 − β(1 − 2^{−(k−n)}) increases with n. So a post-R sub-domain point can miss the pre-R sub-domain by the relative β2^{−(k−k₀)}, and there is no margin for the 𝐇 tails where the layers do not change.
- *A layer-independent set for the R-step's output.* The next T-step's points need only the radius s·α_{1,k}L^{−k}, s = (1+β₀)/L + h_k/α_{1,k}. The R-step's points then need C_H·s ≤ 1 − β, where C_H is the factor by which the minimiser's fine phase can exceed the data's. VAR Theorem 1 gives C_H ~ B₃(d, L)M, which depends on L, and M is large. So C_H(1+β₀)/L ≤ 1 − β is not available.

**What closes it.** A sub-domain stable under Bałaban's construction. One candidate is the space Ũ_k^c with its block-scale conditions and the top-layer parameters on the older layers, scaled to the top-layer fine size L^{−k}. Then (1.65)'s proof applies verbatim ("as for (1.89) [IV]", p.375 l.25–27). SW (b2)'s size must then be redone with the constant B₃M, and (11)(c)(β)/(12)(g) checked for that factor. A second candidate is a Cauchy interpolation between the full-domain analyticity bound and the real-data dev bound. It needs the complex part of the R-step's points to be small against 𝒟_k's older-layer radii, which (1.65) does not give. Both candidates revise the SW closure §3 and the map's (6)(e) margin. Neither is done.

**The SW sub-domain (user: "Go after the SW domain", 03:3x–03:41).**
- With a radius constant in k, the R-step needs C_resp(1+β₀)/L < 1. Here C_resp is the response of the minimiser to its block data, per fine bond at the top-layer size, and the next T-step's points have phase ≤ ((1+β₀)/L + h_k/α_{1,k})α_{1,k}L^{−k}.
- Layer-dependent radii do not help. A radius growing into older layers by C_resp per layer makes the size at a point grow like C_resp^{k−n}, since a* counts the point's own layer without decay.
- A sub-domain parametrised by the determining-set data does not help either: the finer-scale averages of the coarse-data minimiser need the same constant.
- The sources: PRT I p.28–29 bounds the single-scale free H_k by a constant "dependent on d only". PRT II's multi-scale constants (p.247) and VAR Theorem 1's B₃ (p.279) depend on d and L. So the prints do not supply C_resp(1+β₀)/L < 1.
- Not closed. The SW closure is unchanged.

**Note edits.**
- (R-eval)'s "What closes it" (l.10–12) now names C_resp, the set where the post-R clause is needed, the failure of the sub-domain inclusion, and the sources. The line count is unchanged (625, LF, SHA256 462cdf047aa9…).
- The three packets carry the new hash. The eval packet's Q5 asks the reviewer to check the route and the two negative claims, and whether a quotable L-independent bound exists. PRT1, PRT2, and VAR are added to its sources.

## (R-eval): The R-Step Configuration on Λ (28 October, 04:02)

**Read.** LFR II p.365 (1.33)–(1.35), p.366 l.22–25, p.367 (1.40)–(1.45), p.370 (1.50)–(1.54), p.373 (1.61), pp.378–379; PRT II p.247; RG I p.257 l.3; RG II p.3 l.27–28.

**Findings.**
- Off Λ the old and new determining sets and data coincide (p.370 l.7–8). The R-step changes the data only on Λ. On Λ ∩ Ω″^{∼2}_{h+1} they are the averages of U_0^{(AL)}(𝐔), built from 𝐔's k-th averages on Z ∖ Λ and their critical extension V_Λ into Λ. On (Ω″^{∼2}_{h+1})^c they are the real V″ that 𝐓′_k(X) integrates (p.378).
- So on Λ, U_k^0 does not use 𝐔's own data. Its complex part there is the response of V_Λ and U_0(𝐔) to 𝐔's complex data on Z ∖ Λ, bounded in the print by 4d(100M)^5γ_0^{−1}B_3² (1.41) and O(1)B_3B_5M^5 (1.45). Since M = L^m (RG I p.257 l.3; R₁M₁ ≤ M with R₁ a power of L, RG II p.3), these carry at least L^5. So C_resp(1+β₀)/L ≤ (1−β)/2 fails with the printed constants on Λ.
- The identity U(𝐁″_k, M(𝐔)) = 𝐔 for a complexified post-R minimiser 𝐔 would remove the response off Λ. It does not apply: the next T-step's points are not minimisers, since their a″ is a general element of 𝒟^{sub}_{k+1} (SW (b3)). It also does not reach Λ. Not used.
- Bałaban's treatment of complex data inside 𝐓′_k(X) is a first-order expansion around a real configuration with the big analyticity bound (p.379 l.28–37). For the insertions it gives the full-domain bound times the phase ratio, not the small norm.
- L was not tracked through PRT II's proofs: the constants on Λ carry M^5 = L^{5m} in any case, so an L-free multi-scale constant would not close (R-eval) by itself.

**What closes it.** A bound on the response of the critical extension (1.40) and of U_0(𝐔) on Λ, per fine bond, without the factor M^5, together with C_resp for the old-set minimiser off Λ, with C_resp(1+β₀)/L ≤ (1−β)/2. Neither is in the prints. Not closed.

**Note edits.** (R-eval)'s "What closes it" (l.10–12) names the data of U_k^0 on and off Λ, the non-minimiser points, the critical extension's printed constants, and M = L^m. (6C) *The configuration* (l.546) now describes U_k^0's data correctly: the external data off Λ, the averages of U_0^{(AL)} on Λ ∩ Ω″^{∼2}_{h+1}, the integration variables on (Ω″^{∼2}_{h+1})^c ∩ X, and the 𝐇-function data on the boundary layers. Before, it put the integration variables off Λ. The note has 625 lines, LF, SHA256 58f68ee0a420…. The three packets carry this hash; the eval packet's definitions, Q2, and Q5 match the new text.

## (6C) Reviews: Attached Groups, Single-Loop R-Groups, Evaluation Points (28 October, 05:20)

Reviews read in full: two-loops-s6c-att-20261028-r1, two-loops-s6c-single-20261028-r1, two-loops-s6c-eval-20261028-r1.

**Structural consequence (eval, fatal; accepted).** On D(k)(iii)'s 𝒟_k the class is analytic only; its bounds are sup bounds on 𝒟^{sub}_k (SW closure (b2), (b6); D2.6 closure 5.0 *Amendment*, 5.4). So (R-eval) is not a two-loop input only. It reaches D2.7 item 5(b), 15.1, 15.3, 15.6(c), (d) and (f), item 7, and 15.8(c), and with them the single-loop (6.3). Status corrected in the note (header), in D2.7 (an OPEN line at the top, item 5's status, 5(b)), and in the continuum note (an OPEN line at the top).

**att review.**
- S1 (Y_i read as the small-domain Z₀; conflict with D2.7 15.8(c)): accepted. Y_i's χ_k^c(Y_i^{∼−6}) comes from the final decomposition (p.378), not from the preparatory steps (p.385 l.45; LFR I p.181 l.16–19), and 15.8(c) already divides (𝐓′_k(Y_i)1) into quarters. Repair: the D2.6 amendment of l.143, l.146, and l.147 is reverted (¾, with ¼ to Res, ¼ to Pol, and ¼ for the costs). E(Y_i) is paid from 15.8(c)'s third quarter, whose list now names it, with e^{3+2ΣA}E(Y_i) ≤ e^{½(1+β₀)^{−1}p₀(g_k)}. The merge bullet is removed.
- M1 (σ̃ for one-loop groups with carried insertions): accepted. *The weights* uses σ̃(D_g) for every group on one loop, and the one-loop extent bound is the one in *The single loop's R-made groups*.
- M2 (q = 0 clusters at amplitude α^{1/3}): accepted. The repair differs from the review's suggestion. A q = 0 domain contains a whole Y_i (p.389 l.27–28), so these clusters are rooted at one fixed cube of Y_i. Y_i's block words are fixed factors (D2.7 item 7), so the sum is ≤ C_Ψ″α^{1/3} ≤ C_Ψ″ per second-class component, a constant added to E(Y_i).
- M3 (timing): accepted. (𝐓′_k(Y_i)1) is a factor of each term at step k, and the note states the pairing for (6B), the cross carry lemma, and (8.2).
- M4 (the members' extent): accepted; repaired with S2 of the single review.
- M5 (citations), M6 ("(5/2)ν_r ≤ 1"), M7 (drop "contains a first-class component"): accepted and repaired.

**single review.**
- F1 (the factor 16 propagates through untouched insertions) and S4 (later-step domains): accepted. *The units of the members* now bounds a carried member's domain at every later step by (21/20)σ + 17, whatever its factor (at most 17 + σ/4 for u ≤ 16 and L ≥ L₀^×). The 17 is the rounding to whole cubes. It enters σ_g and σ̃ as 17#𝔅(P) and is paid by the margin of (1.89) (*The rounding*: at most 8(105MR_k + 1) members per first-class component, at most 55ν_r each).
- S1 (span cubes): accepted; the review's alternative is used. X_{D_g} is the cubes of ∪dom P with the members' X_W, and span(g) enters only through |span(g)|/M.
- S2 (σ_𝒲 has no payer): accepted. σ̃ carries Σ_W(σ(W) + 17). A member's weight pays σ(W) and its extent; the 17 is a factor e^{17ν_r} on its weighted mass inside 15.7's x_g, which changes a constant in a smallness of g and does not compound.
- S3 (a cross insertion as a member): accepted; D_g is then a cross insertion in the lineage of its first cross member.
- Minors, all accepted and repaired: L ≥ 4800 for u₁ (inside L₀^×); the end-bond box claim replaced by diam_∞(hull g) ≤ 2Σ_Pδ_P; "j ≤ k"; "single-loop member's"; the payment at (5/2)ν_r as in the first case; the extent constant paid by the margin; the D2.7 15.4(i) and 15.7 re-run over X_D, written out (joins as in (6B), the two linear factors under R_k ≥ 17/ν_r, and x_g's exponent); the (T0) window term 50176/c_w; the stale "u ≤ 6"; σ̃ in *The weights*.

**eval review.**
- Serious (the configuration is U_k″, not U_k^0): accepted. (6C) states that the old terms are evaluated at U_k″ ((1.49)–(1.51)), that (1.65) concerns U_k^0 at B = 0, and that placing U_k″ in 𝒟_k is not derived for the insertions, which are covariant only at their ends.
- Serious (the closing route's omissions; U^{𝒦}): accepted. The header's route names U_k″, the mixed data, the Cauchy domain of radius r^{an}_k, and the redone T-step costs under a smaller T_Y. "The same bound covers U^{𝒦}" is removed.
- Minors, all accepted: p.370 l.7–8 (the new set) corrected, with "the 𝐁_k″-minimiser"; p.375's crucial-domain qualifier added; the supports of (1.71) named, and the pre-R indicators shown to be factors independent of (𝐔, 𝐉), so the real points are D(k)(iii)'s base points; R-far″(β) stated; O(1)Lθ ≤ 1 stated; "m ≥ 1" removed; A_k's missing definition as a bound recorded in (6C); the Schwarz-lemma route recorded in one line as not checked.

**Not closed.** (R-eval). The untried route is a Schwarz-lemma response bound from (1.65)'s own domain and range (eval G5).

**Files.** Note 658 lines, LF, SHA256 1222382d9fd9…; D2.7 216 lines, d423cac63c66…; D2.6 177 lines, dac0fd06d585…; continuum note 156 lines, 8148510e764e…. The review packets are not updated, and no re-review is dispatched.

## (6C) Second Reviews Dispatched; the Schwarz Route Checked (28 October, 11:33)

**Dispatched (11:24).** Headless reviews two-loops-s6c-att-20261028-r2 (note l.519–545, D2.7 l.171, D2.6 l.137–147), two-loops-s6c-single-20261028-r2 (note l.280–308, l.429–442, l.546–570), and two-loops-s6c-eval-20261028-r2 (note l.1–38, l.343–360, l.505–516, l.571–583; D2.7 l.1–60; continuum note l.1–8), against the hashes above.

**The Schwarz route (eval G5): it does not close (R-eval).**
- (1.65) maps Ũ_k^c(Y_4, α̃_0, α̃_1) into Ũ_k″^c(Y_1, α̃_0, α̃_1), and the range's radius on an older layer n is that layer's α_{1,n}L^{−n} (LFR I p.190–191, (1.64)–(1.69)).
- U_k^0 is real at real data. For an output bond on layer n, the imaginary part in a chart is harmonic in each slice variable, vanishes on the real diameter, and is bounded by the range's radius. The half-disc harmonic measure gives (4/π)arctan τ ≤ (4/π)τ per unit of the range's radius, where τ is the input's fraction of the domain's radius. The input's fraction is largest on the top layer, about (1+β₀)/L, and the fractions add over the layers.
- So the phase it bounds on layer n is about (4/π)(1+β₀)L^{−1}α_{1,n}L^{−n}. Since α_{1,k−1} ≥ α_{1,k}/(1+β₀) (CRE (2.6)–(2.7)), this is at least (4/π)α_{1,k}L^{−k} at n = k − 1, above 𝒟^{sub}_k's (1 − β/2)α_{1,k}L^{−k}, and of order L^{k−n−1}α_{1,k}L^{−k} below. On the Ω″-layers of the crucial domain, p.190's factor L_0^{2max(0,m−k₀)} makes it larger.
- It gives the top layer only. What is missing is decay of U_k^0's response across the layers. R-dec (map l.219) covers 𝐇(s, tB′), not U_k^0. p.375's "almost the same" regularity is qualitative, and Bałaban names (1.65) as the precise statement, so no reading supplies the decay.
- Repair: the note's header line (l.17) now says this in one line. The edit was made at 11:30, after the eval review started; its reviewer may read either version of l.17. The note's SHA256 is now 1ab0c8f7f3fe….

**Not closed.** (R-eval). What would close it is unchanged: a per-fine-bond response bound C_resp for U_k″, independent of L on the top layer, with decay across the layers, at mixed data, and on the r^{an}_k Cauchy domain.

## (6C) Second Reviews: Triage (28 October, 12:01)

All three r2 reviews were read in full. The single review finished at 11:39, the eval review at 11:41, and the att review at 11:49.

### two-loops-s6c-eval-20261028-r2

No fatal finding. Four serious findings, all accepted and repaired as status corrections.
- S1, the insertions' evaluation point: it is U_k^{(0)}, U_k″ further deformed by LFR I's N preliminary steps (p.181 (1.21), p.191 l.39–41), not U_k″. Repaired in the note's header and *The evaluation points*, D2.7 l.5–10 and item 5(b)'s *Corrections*, and the continuum note l.5.
- S2, the status lines: D2.7 l.3, item 5's status, 15's status, the 15.8 heading, and the "Derived here" list; the continuum note l.3 and l.5; and the (6B) heading, now "(Derived, except (R-eval))". All now carry the exception.
- S3, the base points: the claim that the pre-R indicators are factors of (1.71), so that real data give D(k)(iii)'s real base points, is now marked as a reading. The trace through LFR I (1.3)–(1.9), (1.53)–(1.72) and LFR II (1.70) is a fourth missing item of (R-eval).
- S4, the closing route: it now names U_k^{(0)} with the preliminary chain, all of SW (b1)'s 𝒟^{sub} conditions, the real part as a base point, the base-point trace, and a definition of A_k.
- Minor findings, all applied:
  - only U_k^0 is placed in 𝒟_k (note l.517, D2.7 *Corrections* (b));
  - A_k is removed from the list of bounds and recorded as undefined;
  - the consumer lists are completed, and 15.1 is marked as real-data only;
  - the stale D2.7 line numbers are now cited by item;
  - l.14 now has a″'s part and L^{−k};
  - e^{3+2A} needs A ≥ log(1 + e^{−3});
  - the slot-level u_k″ point is added;
  - p.375 is read "as an inclusion of spaces".

### two-loops-s6c-att-20261028-r2

No fatal finding. One serious finding, checked against the print and repaired.
- S1: 15.8(c) divided (1.89)'s bound on (𝐓′_k(Y_i)1), which is Y_i's persistent factor exp(−κ − 2p₀(g_{j(Y_i)})) (p.384 l.5–6). The later merges and the later (1.89) still use it.
  - Checked against p.378 l.3–8 (χ_k^c(Y_i^{∼−6}) introduced at the R-step), p.383 l.24–28 ((1.79)'s Π′ over components satisfying (i), (ii) with new large fields), and p.385 l.45–p.386 l.2 (the small-domain branch and its new factor exp(−p₀(g_j))).
  - Repair: 15.8(c) and note *The payment of Π_iE(Y_i)* now run D26 7.2's small-domain branch at j = k verbatim. The cost quarter ¼p₀(g_k) of the new factor pays 7.3's costs, e³, and E(Y_i). The e^{2ΣA} is already paid by the κ of the components inside Y_i (M4). The persistent factor stays with Y_i. The arithmetic needed is 3 + p₀/16 + 7.3's costs ≤ ¼p₀ for small g_k.
- Minor findings, all applied:
  - M1: the cases split on "a localisation domain contains Y_i";
  - M2: root count N(Y_i) = 3^d(101R_k)^d + 1, the weight N·N^{−1}, and Ψ's smallness C_Ψ′(1 + 20M)N(Y_i)e^{−p₀/2} ≤ ν_r;
  - M3 and M8: now automatic;
  - M5: the missing size decay e^{κ101^d} is added to E(Y_i);
  - M6: "at most the bound C_νc_CMR_kτ̂_k² on m_k";
  - M7: spanning tree, and the case X′ = Y_i.
- The remark outside scope (ext^{coll}(W) of an att member attached elsewhere) is part of (R-att-ext) below.

### two-loops-s6c-single-20261028-r2

No fatal finding. Three serious findings, all accepted. None is repaired yet; each is recorded as OPEN in the note's header with its route.
- S1 → OPEN (R-round). The member count 8(105MR_k + 1) fails: members made at j < k can have L^{k−j} disjoint intervals per step-k bond. Every payment by the margin of 17#𝔅(P) or of a per-member constant is affected. Route: count the rounding per cube. Members with σ(D) ≥ 640 pay their 17 from their weight; smaller ones lie within 170 π_k-layers of X⁺, a polylog per component; *Join count*'s constant moves to the member's weight.
- S2 → OPEN (R-member). Cross members of single-loop groups can belong to several groups, and their payment is not derived. Route: a merge rule.
- S3 → OPEN (R-att-ext). The att collar is unspecified, Y_W's distance is uncontrolled, a max should be a sum, and the att members' 17s have no payer. Route: the first att member's collar, distance through diam_∞T_W, sums, and (R-round)'s payer.
- These OPEN items are propagated to D2.7 l.5–10 and the continuum note l.5, since the single loop's (6C) groups supply D2.7 15.6–15.7.
- The minor findings (the factor 16 at every later step, u = 1 for T-step descendants, (H0)'s Cov domains, 15.7's polymer part, the share's ext term, the production-units citation, the step-1 alternative, and the two uses of c_w) are left for the (R-round) rewrite, which touches the same lines.

**Hashes after the repairs:** note eb6bed14bf6f… (689 lines), D2.7 f3889aeeaa3b… (221 lines), continuum note 302d20f45aaf…. No re-review dispatched.

**Not closed.** (R-eval), (R-round), (R-member), (R-att-ext).

## (R-eval) Base-Point Trace: Review r1 Triage (28 October, 14:03)

The review two-loops-reval-base-20261028-r1 (headless, claude-opus-5-5, effort high) ran 13:39–13:56 on the note's *The real base points* (then l.53–70), its l.659, and D2.7 closure l.7. Input hashes matched (note aa17b520acb1…, D2.7 b0c6fbd2f7dc…, map 423516f1ea57…). The reviewer labelled itself context-exposed, because AGENTS.md was injected. The report was read in full.

No fatal finding. Three serious findings, all checked against the print and repaired.
- S2, the operations: the list of four kinds left out Bałaban's exact integrations (1.60)–(1.62) of the preliminary fields with (1.63), the localisation expansions (LFR II p.372, p.377), the change of variables (1.22) [III] on the 1 − χ′^{(j)} components, and the R′-replacement (1.100), which is not a gauge fixing.
  - Repair: six kinds. The integrand that carries the insertions keeps (A_j, B_j) as integration variables, with χ^{(j)}, χ′^{(j)}, and (1.6). It is Bałaban's integrand times the insertions' normalised average over them, so the pointwise correspondence holds. (1.53) and (1.81) (p.195) are now named as the changes of variables, and the AL-gauge compensations of p.197 l.39–42 as gauge operations.
- S3, χ′_j: the step χ′^{(j)} ⇒ χ′_j used the literal threshold |B_j| < δ′_j, which `TRANSCRIPTION_FINDINGS.md` (LFR II p.383: "|B(b)| ≥ g_j^{−1}δ′_j = A₁p₁(g_j)") identifies as unit-scale.
  - Checked: p.188 l.8–9 excludes the 1 − χ′^{(j)} components; p.188 l.53 gives exp i[g_jCB_j − hD̃(g_jCB_j)]; RG I p.267 says D̃ begins with quadratic terms; (1.38) gives δ′_j/δ_j = p₁/p₀; p.186 l.40 gives the factor 8B₃γA₁p₁(γ).
  - Repair: χ′_j is not a pre-R indicator. On supp χ′^{(j)}, |V_j(V_Z^{(j)})^{−1} − 1| ≤ c′δ′_j with c′ = c_C + 2. Each use of χ′_j's 2δ′_j in the proof of (1.29) ((1.5) at p.184 l.17–19, (1.38), (1.43), (1.45), and (1.54)) then holds for g small given d and L. This is now marked derived.
- S1(b), the induction: "this bullet carries it through each R-step" was not the needed link.
  - Repair: the pre-R clause is the T-step's (map l.174) on a term of the CRE Sect. 2 form. After an R-step that form is LFR II Theorem 1's (accepted), with the base points entering the next T-step as in D2.7 15.8(e). The bullet now says it uses the pre-R clause and does not derive the post-R one.
- Minor findings, all applied:
  - the headline, l.9, l.19, (6C) (now l.681), and D2.7 l.7 now say "a G-valued gauge transform of a real base point", which satisfies the real-U parts of (2.34) and (2.38). The Conclusion records that (1.5)–(1.9) are not gauge invariant (p.179 l.2–3);
  - (6C)'s second-class case is corrected: the indicators are removed there, and χ_{k,Λ}χ is what is kept;
  - D2.7 l.7 now lists (1.22)–(1.23), and the χ′ step is listed as derived;
  - (1.29) is quoted with χ(Z_{j+1}∩Ω_{j+1}) and ζ(Ω^c_{j+1}) on the left-hand side only;
  - S is defined by the indicator factors, with (1.6) as a density and 𝕋_k(Z_k∩Z^c)'s indicators added;
  - the scope conditions are recorded: β ≤ 1/4, (1.94)'s conditions on N, p.200 l.30's 1/4, δM/M₁ ≥ 2, γ small, and L₀² ≤ L/3;
  - p.181 l.20–22; "hD̃"; the factors left now include the second-class and the preliminary-variable factors; "combine[s]" is read as a product;
  - LFR I Proposition 1 is assigned to U_0's V_Λ.

**Hashes after the repairs:** note 4250a957b56b… (765 lines), D2.7 f2c70ec12d84… (221 lines). No re-review dispatched.

**(iii) on Z's older layers: a route.** The note's (iii) now carries a route that needs no localization of ℍ^{(n)} in the background.
- LFR I (1.44) makes ℍ^{(n)} VAR's 𝓗-function, with the collar difference s as its argument. VAR Proposition 9 (p.309) bounds the data derivatives by (190), uniformly on the ball (172), |B′| < 2C₁ε₁. Theorem 1 needs only M′ε₁ ≤ a₁ (p.305 l.6), so the radius is g-independent.
- With both stages written at one real background, the step's increment vanishes at s = 0. The Schwarz lemma in s gives a factor O(δ′_j) per step, and e^{O(Nδ′)} over the N steps.
- Three checks remain, listed in the note. The route is not yet derived.
- Note hash after this edit: 9fe8b0c00136… (776 lines).

**Not closed.** (R-eval) (iii) on Z's older layers (route recorded), (R-round), (R-member), (R-att-ext).

## (R-eval) (iii) on Z's Older Layers: The Route Derived (28 October, 14:43)

**Checks run.**
- VAR's setting: Theorem 1's (7) uses one ε₁ for all layers, and a₀, a₁, B₃ depend on d and L only (p.279). (172) makes B dimensionless, and H₀B minimises on L^{j(·)}ηQA′ = B (p.297 (129)). (190) is printed as a result with its calculation omitted (p.308 l.25–27); it is accepted from Bałaban.
- LFR I applies VAR's representation to its stage configurations ((1.30), (1.34), (1.44)–(1.45), B₃ at p.191 l.28); accepted from Bałaban. The u-free chain's source is g_jCB_j − hD̃(g_jCB_j), real and background-free (p.191 l.39–41).
- The step increment F(Δd, s) vanishes at s = 0 and obeys (190) composed once with M^j. The Schwarz lemma in s gives O(δ′_j) per step, and the stages are functions of the same external Δd, so the N steps add. The sum is O(N^{1+β₀}δ′_k)S_Lλα_{1,k}L^{−k}, below ⅛(1−β)α_{1,k}L^{−k} for g small. S_L is finite once δ₀M/(16M₁) ≥ (d + 1)log L + 1.

**Result.**
- The deformations' phase on Z's older layers is derived, except one gauge bound. The u-free factor and the stage minimisers' Landau representative at the real base differ by a G^c gauge transformation g. Its complex part would need |Im g| ≤ O(1)L^iη·λα_{1,k}, and VAR p.307 states only that g is analytic.
- New open item, found in this check. SW (b1)'s sub-domain has three conditions: the phase, the covariant gradient, and 𝐉, all in the scale-k weight on every layer. The (R-eval) bullets had checked the phase only.
  - On Z's older layers the deformations' complex gradient is O(δ′_j)λα_{1,k}L^{k−i} in that weight near complex data on the collar's layer. The source is the collar's fluctuation field, rough on the block scale, so the size is real.
  - k − i runs to N = R_j, so this exceeds the room.
  - The transported part's and the response's gradient and 𝐉 conditions are not checked. LFR I (1.98)'s first line bounds the response's plaquette term in the top weight, M⁵e^{−δ dist}ε_kη².
  - The 𝐉 coordinate at the evaluation points is not specified in the note.
- The note's membership claims are restated as the phase condition: header, derived list, *The R-step lands in the family*, (i), (iii), (iv), *A_k*, l.106, and *What it does not give*. A_k uses only the phase.
- D2.7 l.7 and item 5(b) name the two open parts.
- What would close the gradient part: either show that the complex data near Z's old collars lie on enough newer layers, or weight SW (b1)'s gradient and 𝐉 conditions by the layer, normalised to the top-layer radius, and re-check their consumers. The consumers found are SW (b2)'s Schwarz radius (SW l.92), which needs only layer-weighted room, and j*'s r_J (map l.318).
- Hashes: note 09f6761506b1… (778 lines), D2.7 f37ccc56d270… (221 lines). No review dispatched.

**Not closed.** (R-eval): the gradient and 𝐉 conditions, and (iii)'s gauge bound. (R-round), (R-member), (R-att-ext).

## (R-eval) (iii): Is the Gauge Bound Needed? (28 October, 15:14)

The user asked: "Why do we need information about the gauge transformations? Isn't everything new we are estimating gauge invariant". The chat answer proposed dropping the bound, since the evaluated words are gauge invariant. The user approved a rewrite on that basis, to be made if the check held. The check holds in part.

**Checks run.**
- VAR p.281 and Proposition 2: the Landau representative is reached by the unique gauge transformation u with \overline{R_0u}^j = 1 on every Λ_j, and it satisfies the data condition (20). REG pp.80–83 (Section C, (1.29), (1.33)–(1.39), Theorem 2) states the same for real configurations. REG Theorem 2 bounds the Landau representative A, not u.
- VAR p.305 (172)–(174) and p.307 (181): exp iη𝓗(B) is this representative of U_k(V′V₀) relative to U₀. The Landau-to-axial transformation is analytic in 𝓗, and (181) extends the minimiser to G^c orbits. No bound on the transformation is printed.
- CRE p.261: membership in Bałaban's spaces is a condition on a representative 𝐔 = U′U with U real. The spaces are invariant under G-valued gauge transformations only, and 𝐉 transforms by the adjoint representation.
- The note's *The transport form*: Φ(𝐔) = E(𝐔)𝐔 keeps 𝐔's own frame, and the transported part and the response are bounded there.

**Result.**
- What holds: the steps compose in one frame. The u-free chain's stage configurations and the data route's are Landau representatives of the same minimisers with the same block data, so each step's source sits on the same data in both. The words do not depend on the representative.
- What does not hold: dropping the bound. The bounds depend on the representative. The transported part and the response are bounded in Φ's frame, and the data route's increments in the Landau gauge at the real base. Combining them conjugates each increment by g, the gauge transformation between the background's two representatives, and that conjugation needs |Im g| ≤ O(1)L^iη·λα_{1,k}. Evaluating at the Landau representative instead would need the transported part and the response re-bounded in that gauge on every layer. That includes the newest layer, where λ^{(k)}_k = 1.
- The chat claim that the two representatives "differ by a real gauge transformation at real configurations, so the bound drops" is correct for the words and does not reach the bounds.
- The note's "g = 1 at real data" is restated as "g is G-valued at real configurations, and g = 1 at 𝐔 = U".

**Note edits.**
- l.8 (the open item) names g as the transformation between the backgrounds' representatives in the transport form's frame and at the real base, and says why the bounds see it.
- (iii) *The gauge representatives* is split into four sub-bullets: *The steps compose in one frame*, *The bounds depend on the representative*, *The bound needed*, and *Evaluating at the Landau representative instead*.
- A new sub-bullet, *What would close the gauge bound*, has two parts. One is a bound on the derivative of the Landau gauge fixing, local on the block scale with decay across layers, like (190) (REG Section C with the propagator bounds of [4]). The other is an induction over the steps, each adding O(δ′_j) times the current complex phase, which compounds to exp(O(N^{1+β₀}δ′_k)). The old *What would close it* is renamed *What would close the gradient and 𝐉 conditions*.
- Hash: note 311de6c9eefc… (783 lines). D2.7 is unchanged, since its wording, "a gauge bound for the deformations on Z's older layers", still holds. No review dispatched.

**Not closed.** (R-eval): the gradient and 𝐉 conditions, and (iii)'s gauge bound. (R-round), (R-member), (R-att-ext).

## (R-eval) (iii): The Gauge Bound Derived (28 October, 16:58)

The user asked: "Derive the gauge bound: read REG Section C and the propagator bounds it uses, bound the derivative of the Landau gauge fixing with respect to the complex part, and run the induction over the steps."

**Sources read.**
- REG pp.79–81 ((1.27), (1.29), (1.30)) and pp.89–94 ((1.77), (1.90)–(1.109), Proposition 5).
- PBG pp.393–400 and 413–416 ((3.25), (3.35)–(3.37), (3.41), (3.44), (3.47)–(3.49), Theorem 3.4).
- VAR p.279 (Theorem 1, (9)–(10)), p.305, and its applications of PBG at pp.285, 295–297.
- CMP98 p.50 ((209)–(214)), PRT2 p.234 (Lemma 2.1), LFR I p.186 ((1.45)) and p.191 l.36–48.

**Correction.** The 15:14 section's "the steps compose in one frame … with the same block data" is wrong. By REG (1.30) a Landau representative's block variables are the configuration's conjugated by u at the block points, so a representative does not keep the block data. The u-free chain's sources and data reach the Landau gauge rotated by G and u, and the derivation tracks these shifts (term (b) of *One step's deviation*). The sub-bullet *The steps compose in one frame* is removed from the note.

**Route.**
- The induction runs on the stage deviation ε_n from the real chain, in Φ's frame, with each step compared in the Landau gauge at its own real base U₀.
- G, from Φ's frame to the Landau gauge, is a fixed point with a sup-norm source: |λ̂|_{(1)} ≤ 2B_Gε through G′RD*, which is first order. |Dλ̂|_{(0)} comes from Dλ̂ = A_L − N(λ̂), with A_L controlled by VAR (190), and continuity along 𝐔_t excludes the large branch.
- u, from the stage-n configuration to its Landau representative, is REG Proposition 5's fixed point one weight up. Its source Θℍ′ + R₀D*₀B₂ is in the (−1)-norm by LFR I (1.45)'s gradient entry and (190), and ∇G′ then gives |Dμ|_{(0)}.
- A first attempt at u, with the fixed point at the complex base 𝕎 and only (1.45)'s sup entry, failed: the remainder η|X||Dμ| needed |Dμ|_{(0)}, which that scheme could not bound. (1.45)'s gradient entry, which the note had quoted only for its sup entry, closes it.
- An earlier version of the G lemma bounded |DG′RD*A|_{(0)} by |A|_{(0)} through ∇G′∇*. PBG bounds that only in a Hölder norm ((3.44)), and the lemma was rewritten without it.
- Each step adds dev_n ≤ C_*S_L²δ′_jε_{n+1}. The product over the N + 1 steps is at most 2, and the sum is O(N^{1+β₀}δ′_k)S_L²λα_{1,k}L^{−k} < ⅛(1−β)α_{1,k}L^{−k} for g small.

**Weak points named for a reviewer.**
- R's (γ)-norm bound for γ ∈ [−2, 0], and the weighted bounds of K, Q′, and C, are derived from (3.47)–(3.49) with PRT2's layer sums, not printed; REG (1.98) prints only γ = −2.
- The one-weight gain of δG′, δC, and δR in the base change Θ is derived here, from the zeroth-order differences and Q′'s averaging (PBG p.393).
- CMP98 (212)'s error terms are read in the weighted norms, with |λ̂| ≤ |λ̂|_{(1)}L^lη at scale l.
- The identification of 𝕎 and 𝕎_n with VAR's 𝓗 at complex 𝐔 is by analytic continuation from real points, with VAR Theorem 1's uniqueness there.
- ε_Φ's bound along the segment 𝐔_t uses only the phase of A′; the 𝐉 coordinate at the evaluation points is still unspecified.

**Note edits.**
- The OPEN header and *What is missing* name only the gradient and 𝐉 conditions; the gauge sub-bullet is removed.
- The "(iii)'s gauge bound" qualifiers are removed from the derived list, *What would close it*, the remaining parts' (i), *A_k*'s evaluation points, the closing line of *The remaining parts*, and *What it does not give*; the derived list names the new inputs.
- (iii): the heading, the header of *On Z's layers m ≤ k₀*, and the (1.45) quote, now with its gradient entry, are updated. *One step* and *The Schwarz bound* are restated relative to the step's Landau representative and ε_{n+1}. *The gauge representatives (derived)* has seven sub-bullets: *The base*, *The Landau representatives*, *The bound on G*, *The base change*, *The bound on u*, *One step's deviation*, and *The induction*. *The sum* is restated with S_L² and ε_Φ ≤ 2λα_{1,k}. *What would close the gauge bound* and *Evaluating at the Landau representative instead* are removed.
- D2.7 l.7 and l.61 name only the gradient and 𝐉 conditions as open.
- Hashes: note 0d212101123b… (788 lines), D2.7 9223ab65f631…. No review dispatched.

**Not closed.** (R-eval): the gradient and 𝐉 conditions. (R-round), (R-member), (R-att-ext).

## (R-eval): The Gradient and 𝐉 Conditions, and a Scope Problem (28 October, 17:54)

The user asked to skip the review for now and work on the gradient and 𝐉 conditions.

**Sources read.** SW closure (b1)–(b4), (6b), (6c), and §2 (q₀ = q₁; C₀, C₁ "sufficiently large", no ratio). Map l.317–318 (j*, r_J), (6)(e) *Older layers* (l.929), l.1344, l.1372. RG1 pp.262–263 ((1.8), (1.10), (1.15)–(1.17), (1.19)). CRE p.261 ((2.34)–(2.39), G-invariance only, l.43). VAR pp.308–309 ((190), Proposition 9). LFR I pp.190–191 and 197–200 ((1.64)–(1.69), (1.98)). LFR II pp.374–375 ((1.65)). PBG p.397 l.37, p.423 l.39, p.432 l.39 (δ₀, B₀ depend on d and L only).

**Derived.**
- The layer-weighted gradient and 𝐉 conditions: CRE (2.39) and (2.36) with α_{i,n} replaced by λ^{(k)}_nα_{i,k}L^{n−k}. In PBG's norms these are |∇A′|_{(−1)} < λα_{1,k} and |𝐉 − J|_{(−2)} < λα_{0,k}, which are (190)'s weights. The family stays inside 𝒟_k, for α₀ through (6)(e)'s form of CRE (2.6)–(2.7).
- The consumers re-checked: (b2)'s j* with the weighted r_J, (6b)'s and (6c)'s Schwarz radii (Bałaban's layer radii suffice), (b3)'s transfer (ratio ½(1−β) for the gradient, ½(1−β)(1+β₀) ≤ ¾(1−β) for the current), (b3)'s 𝐇-part (top-layer weights imply the layer weights), and (b4).
- The reduced frame: the representative 𝕎_n^G = (𝕌^{(n)})^{ũ^{−1}}, ũ = GuG^{−1}, has step factor Ad_{G₋}e^{iηX} exactly. Term (d) and the μ-part of E drop out.
- The deformations' gradient and current on every layer, through (190)'s gradient and D*D entries, with no factor L^{k−i}. This is the factor that made the gradient look open.
- The 𝐉 coordinate at the evaluation points (quoted): the holomorphic current of the evaluation configuration, from RG1 (1.15)–(1.17).

**Corrections.**
- (a) The note's sentence that f_n = 1 − β(1 − 2^{−(k−n)}) is no smaller before R is wrong: f_n is no larger. The conclusion holds, since the transported bound carries no f_n and f_n ≥ 1 − β.
- (b) The scope problem. (ii)'s gluing and *The Landau representatives*' continuation used the real points as a uniqueness set. The identities Φ(U) = U_k^0(M(U)) and 𝕎 = e^{iηA_L}U₀ hold only at real post-R minimisers. Those form a totally real submanifold of maximal dimension of 𝓜^c, not of the T-step's open set. The T-step's points include real non-minimisers (a″ real ≠ 0, or s ∈ (0, 1)). So every bound of (i)–(iii) holds on 𝓜^c only. The analyticity of (ii) is unaffected, since it is taken at Bałaban's configuration.
- (c) The repair, and its cost. The old insertions' function depends on 𝐔 only through M(𝐔), so the bound at 𝐔 is the bound at P(𝐔) = U^{post}(M(𝐔)) ∈ 𝓜^c. P(𝐔)'s complex part is the minimiser's response to 𝐔's data, at most K = O(C_dS_L) times 𝐔's room by (190). Landing needs L ≥ 2K(1+β₀)/(1−β), and the current also needs C₀ ≥ O(K)C₁ on the newest layers. K depends on L through δ₀(d, L), B₀(d, L), and (190)'s O(1).

**Weak points named for a reviewer.**
- The transported part's gradient needs E(U) to be a smooth field off Λ, i.e. U_k^0(M(U)) and U in one gauge. Its current needs D*D of the data's complex part, which the family does not bound.
- (1.98)'s response term bounds the response's curl, not its full gradient.
- The complex curvature conditions (2.34), (2.35), and (2.37) at the evaluation points are not checked.
- The real conditions at P(U) for real non-minimisers U are not checked.
- The candidate single evaluation at P(𝐔) needs the chain's final stage to be one VAR minimiser of all its data, which is not checked against LFR I (1.30), (1.34), and (1.44).

**Note edits.**
- The OPEN header, *What is missing*, a new *What would close it*, the derived list, and the lead of *The derivation* (formerly *What would close it*) are rewritten.
- *The dilated sub-domains* gets the layer-weighted conditions, the inclusion for α₀, the transfer of all three conditions, j*'s radius, and *The consumers of the gradient and current conditions*.
- The f_n sentence is corrected, and the phase conclusion is restricted to 𝓜^c. The remaining parts' (i) and the (iii) headings are updated. (ii)'s gluing sentence is replaced. *The Landau representatives*' continuation is restricted to 𝓜^c.
- *The gradient and 𝐉 conditions (OPEN)* and *What would close the gradient and 𝐉 conditions* are replaced by *The scope*, *The reduced frame*, *The gradient and the current of the deformations*, *The 𝐉 coordinate*, and *The transported part and the response*.
- The closing line of *The remaining parts* and *What it does not give* are updated.
- D2.7 l.7 and l.61 name the new open part.
- Hashes: note 3f79c0a70e0f… (823 lines), D2.7 eaff567b94d1…. No review dispatched.

**Not closed.** (R-eval): the factor K off 𝓜^c, the gradient and current at the start of the chain, the curvature conditions, and the real conditions at P(U). (R-round), (R-member), (R-att-ext).

## (R-eval): Four Reviews Triaged, and the Factor K Against L (28 October, 18:44)

Reviews: `two-loops-reval-weighted-20261028-r1` (the dilated sub-domains, l.33–44), `two-loops-reval-gradcur-20261028-r1` (the reduced frame, the deformations' gradient and current, and the 𝐉 coordinate, l.89–100), `two-loops-reval-scope-20261028-r1` (the OPEN line and the scope, l.5–11, 59, 84–88, and 101–104), and `two-loops-reval-gauge-20261028-r1` (Z's older layers, l.63–83). All four were read in full. None reports a fatal finding.

**Weighted review.**
- Serious 1 (D2.6's att bounds on 𝒟^{sub} not re-checked): accepted in part. D2.6 §5.4 uses only the phase condition. With λ^{(k+1)}_n ≤ c′^m, its transport factor ((1+β₀)/L)^m gives ((1−β)/2)^m ≤ 1, and its condition becomes 4c_πMλα_{1,k+1} ≤ 1 (g small). §5.1 uses 𝒟^{sub} as the clause's domain and the chain condition, which the transfer gives. Repaired: a new sub-bullet under *The consumers*, and "only" removed.
- Serious 2 ((2.36) is centred at 0, the family's current at J_k): accepted. At the T-step's points map (6)(e) gives it (l.928–929, via R-m). At the R-step's evaluation points it is added to the OPEN line.
- Minors: the clause is now asserted on 𝒟^λ_k (minor 4); the i = 1 factor is cited to map l.696's one-step bound (minor 6); "only" is fixed (minor 7); the two c′ are separated (minor 9, see the gauge review's m1). Not edited: j*'s ϱ as the family's top-layer-normalised radius (minor 1), the 𝐇-part's current in the ¼(1−β) leftover (minor 2), λ in 2ρ_k and 𝔞_{k+1} (minor 3), the factor λ^{(k)}_n in "weaker by" (minor 5), J_k against J_{k+1} (minor 8), and f^{(k+1)}_n and R(u)J_{k+1} (minor 10).

**Gradient-and-current review.**
- Serious 1 (D*D of (c′) needs ∇∇λ̂): accepted. (190) prints ∇, D*D, and Δ, not ∇∇. The deformations' current is now OPEN, with the covariant route (J^h at the reduced representative, which needs only |λ̂|) named.
- Serious 2 (the data's own 𝐉 enters): accepted, and confirmed in the print. RG1 p.275 l.3–4: "The variable 𝐉 replaces the function J_{k+1} as usual"; LFR II p.375 l.11–12 introduces (𝐔, 𝐉) into the other expressions "in the usual way". The bullet is relabelled a reading, and the data's 𝐉 is added to the OPEN line.
- Minors: (e^{2|λ̂|} − 1)|X| for 2|λ̂||X| (minor 7, first item), the term O(γ₀ε₀) (minor 5), and the RG1 citation, now p.262 l.59–p.263 l.2 under (1.16), with (1.8)–(1.9) checked on p.261 (minor 6), are fixed. Not edited: G → G^c continuation's domain (minor 3), γ_Φ in κ (minor 4), "ηℍ", O(1) in place of O(B₃), and the Hessian bound η|∇∇f| ≤ 2|∇f| (minor 7).

**Scope review.**
- Serious 1 (the 𝐇-part against K off 𝓜^c): accepted and added to the OPEN line. The reviewer's β ≤ 1/(2K − 7) is not re-derived; the note states only that it bounds β in terms of K, or needs T_Y reduced by K.
- Serious 2 ((1.65) is the wrong citation for the factoring through M): accepted. The factoring is Bałaban's own: "We replace M·(U_k), V″ by the corresponding M·(𝐔), and V_Λ^{(A)} by the function V_Λ^{(A)}(M^k(𝐔))" (LFR II p.374 l.39–40). Its regularity off Λ^∼ is "almost the same as for the configuration U(𝐁_k″(Y₁), M·(𝐔))" (p.375 l.12–13), and (1.50)'s data off Λ are the new configuration's (p.370 l.4–8). l.87 now cites these.
- Serious 3 (Bałaban's devices against C₀ ≥ O(K)C₁): resolved below.
- Minors: "on every uncapped layer" (minor 1) is fixed. Not edited: the scope's room qualifier (minor 2), the relative error in l.85 (minor 3), the layer leakage in K (minor 4), "up to gauge" (minor 5), and the response's K (minor 6).

**Gauge review.**
- S1 (the identities of *The Landau representatives*): accepted. A representative keeps its block data only in REG (1.31)'s double-bar averages, 𝓗's argument is the axial-gauge minimiser's data, and VAR Theorem 1's uniqueness is of orbits. Marked OPEN in place, in the heading of *On Z's layers m ≤ k₀*, in the derived list, and in the OPEN line. The expected route is Schwarz in s, since X vanishes at s = 0. Not derived.
- m1 (three c′): fixed. l.6's c′ is removed, and l.134's constant is renamed c_χ at l.68, l.78, l.81, l.91, l.97, l.134, and l.136 (old numbering). Not edited: m2–m11, and (130)'s page.

**The factor K against L.**
- In print K's constants depend on d and L. B₃ "depend[s] on d and L only" (VAR Theorem 1, p.279 l.28), and Bałaban's "absolute constant" includes L (VAR p.299 l.26). δ₀ is (d, L) (PBG p.397 l.37). The multi-layer free constants depend on L through γ₀′ = π²/L² (PRT II p.242 l.42–43; Proposition 2.5, p.246). Only the free single-scale kernel's constants depend on d alone (PRT I Proposition 1.2, p.35).
- Bałaban never needs L against B₃. His spaces bound the data-minimisers only through curvature and current at the level α₀ (CRE (2.35), (2.37), p.261; RG1 (1.16), p.262 l.52; LFR I (1.68)). He absorbs B₃ by an inner constant: "for α₀′ sufficiently small the above estimates imply the condition (iv)" (RG1 p.263 l.18). α₀ and α₁ are fixed after M (RG1 p.264 l.38–41). In his re-minimisations, LFR I (1.44)–(1.48), B₃ multiplies the small increment δ′_j, and the products are made at most αβ by γ or A₁/A₀ (p.186 l.35–42). The phase of a data-minimiser at the level α₁ is asked only by the note's class.
- The current part closes by a choice. C₀ ≥ C_KC₁, with C_K = O(K)/(1−β), is fixed after L and M. CRE (2.28) asks only "sufficiently large" (p.259 l.50), SW (c2) leaves the ratio free, the map's l.1372 needs only α₀/α₁ bounded, and K does not depend on C₀ or C₁. For review, as SW (c2) is.
- The phase and gradient part stays OPEN: L ≥ 2K(1+β₀)/(1−β). RG1 p.275 l.9–10's "approximately the same regularity properties as 𝐔" and LFR I (1.68)'s c = 3 on the top layer carry no constant for K. The route is K ≤ K₀(d) + o(1) as M → ∞ and g → 0. K₀ comes from PRT I's single-scale kernel, the interfaces are paid by the crossing cost M/M₁, and the background corrections are O(α₀). Not derived: the newest layer's kernel within a few blocks of its interface with the older layers.

**Weak points named for a reviewer.**
- The current part's choice C₀ ≥ C_KC₁ rests on nothing in the chain needing C₀/C₁ bounded independently of L. That was checked against SW (c2)–(c3), the map's l.1372, and the note's j*, but not against D2.3–D2.6 line by line.
- The route for the phase part assumes that PRT I's single-scale bound transfers to the layered, background-dependent kernel away from the interfaces. That is not checked.

**Note edits.**
- The OPEN line: *What is missing* gains the printed (d, L) sources, five new items (the deformations' current, the Landau-representative identities, the data's 𝐉, (2.36) about 0, and the 𝐇-part against K), and "every uncapped layer". *What would close it* is split into the current part (closed by the choice), the phase and gradient part with Bałaban's devices, the route, and the single evaluation.
- The derived list: the older layers' phase is conditional on the identities, the deformations' current is OPEN, the 𝐉 item is the configuration's part, and the current part of K is added.
- *The dilated sub-domains*: 𝒟^λ_k as the clause's domain, map l.696's citation, "only" removed, and the D2.6 sub-bullet.
- *On Z's layers m ≤ k₀*: the heading, and an OPEN sub-bullet under *The Landau representatives*.
- *The scope*: l.87's citation. *The reduced frame*: (e^{2|λ̂|} − 1)|X|. *The gradient and the current of the deformations*: the heading, the OPEN sentence, and the γ₀ε₀ term. *The 𝐉 coordinate*: relabelled, the citation, and the data's 𝐉.
- c_χ for l.134's constant. The closing line of *The remaining parts* lists the OPEN line's items.
- D2.7 l.7 and l.61 name the new open items.
- Hashes: note 172addfcfb5f… (835 lines), D2.7 2a91e8079a51…. No review dispatched.

**Not closed.** (R-eval): the phase and gradient part of K, the gradient and current at the start of the chain, the deformations' current, the Landau-representative identities, the data's 𝐉 and (2.36) about 0 at the evaluation points, (b3)'s 𝐇-part against K, the curvature conditions, and the real conditions at P(U). (R-round), (R-member), (R-att-ext).

## (R-eval): Why Bałaban Needs No K (28 October, 18:54)

**Correction.** The previous section's "The phase of a data-minimiser at the level α₁ is asked only by the note's class" is wrong. Bałaban's old activities are evaluated at data-minimisers too: RG1 (3.24)–(3.25) (p.275) evaluate 𝐄^{(j)} at U_j(□₀, M·(…U_{k+1}(□₀, M·(𝐔)))), on a space with phase room (1+2β)α₁.

**His device.** He splits the data before minimising. M·(𝐔) = V^v in a generalized axial gauge, with |V(b) − 1| < O(1)Mα₀ and |v − 1| < O(1)Mα₁ ((3.26)). U_{k+1}(□₀, V) = (exp iL^{−1}η𝐇_{k+1}(□₀, (1/i)log V))^{u_{k+1}}, with 𝐇_{k+1} and u_{k+1} − 1 bounded by B₃O(1)Mα₀ ((3.27)). v and u_{k+1} are removed by the invariance under G^c gauge transformations near G, applied to 𝐉 and B as well ((3.28)–(3.29), p.276). So the minimiser's response constant B₃ multiplies only the curvature-sized contour data V; the phase sits in v and is never amplified.

**Why the note has K.** *The scope* bounds P(𝐔)'s complex part as 𝓗^{post}(Δd), with Δd the whole complex data in the Landau gauge relative to the real minimiser. That feeds the pure-gauge part of the phase to the minimiser, and K multiplies the full phase room. The scale gain per step is only (1+β₀)/L, hence L ≥ 2K(1+β₀)/(1−β).

**Route (not derived).** The same splitting for the class, whose words are G^c-invariant. It needs a complex-curvature condition on 𝒟^λ_k smaller than the phase room by O(B₃M), with that ratio fixed after L and M, as (3.26)–(3.27) need B₃O(1)Mα₀ inside the phase room. K's current part is then to be re-derived by covariance against the curvature condition. That may reverse the choice C₀ ≥ C_KC₁ of the previous section, since the splitting asks curvature small against phase. K ≤ K₀(d) + o(1) stays as a fallback.

**Note edits.** *What would close it*: the phase and gradient bullet and the route bullet are rewritten with (3.24)–(3.29). Hash: note 33ecab48122c… (835 lines). No review dispatched.

## (R-eval): The M-Factored Domain Removes K From L (28 October, 19:09)

**Why the splitting was not used.** On 𝒟^λ_k the gradient room equals the phase room in scaled units, so the curl of A′ is as large as the phase room. The axial splitting would put a curvature of phase size into V, where B₃ multiplies it. The splitting alone does not remove K for this class.

**The derivation.** Bałaban's T-step is M-factored (RG1 p.275 l.1–6). The class's domain is taken the same way: 𝒟^{λ,M}_k := {𝐔: M(𝐔) within VAR's radius, P(𝐔)'s Landau representative in 𝒟^λ_k}. The old functions depend on 𝐔 only through M(𝐔), so the sup bounds there are those on 𝓜^c ∩ 𝒟^λ_k. At step k+1 the background is P_{k+1}(𝐔).
- At s = 1 the consumer's point e^{iη𝐇(1,tB′)}P_{k+1}(𝐔) is a step-k minimiser (RG2's U_k(e^{iB′}V) = e^{iη𝐇}U_{k+1}, map l.108 (ii), extended to 𝓜^c by analyticity). P is the identity there, and SW (b3) lands it under L ≥ 2(1+β₀)/(1−β) alone.
- At s ≠ 1 the data differ by 𝐇(s,tB′) − 𝐇(1,tB′), so the response is at most 2K sup|𝐇|.
- T_Y reduced by 4K: 1/T_Y := max(|B′|_Y/ε_H, 64KB₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k})). Then (1+2K)h_k^{(K)} ≤ min(β,1)α_{1,k}/4 for g_K small under q₁ > p₀, below map (6)(e)'s h_k, so SW (b3) and map l.707 cover it on every layer, real points included.
- D2.4: C_T ≤ 4K·C_T enters only θ_k's (β) term, which is ≤ 1/4 for g_K small under (R-m′) (map l.1581–1582). g_K is fixed after L and M.

**Weak points, checked.** K is fixed after L and M (printed constants (d, L) plus M), so absorbing it by g_K small is legitimate. The response bound uses Proposition 9 with a complex base point (the s = 1 minimiser), at relative error O(sup|𝐇|/r_B), as in *The scope*. The current's response is K times the phase room, so C₀ ≥ C_KC₁ stays, for review. The identification of RG2's U_k with the post-R minimiser U^{post} at the T-step's s = 1 points is not derived: map l.108 (ii) states U₁(e^{iB′}V) = e^{iη𝐇}U₂ for the small-field minimiser only, and the post-R determining set 𝐁_k(Y₁) has not been checked against RG2. It is added to the note's OPEN line.

**Note edits.** OPEN line: the K paragraph replaced by the M-factored statement; the items "(b3)'s 𝐇-part against K" and "the real conditions at P(U)" removed (derived). *What would close it*: the two K bullets replaced by one. Derived list: the phase and gradient part of K added. (iii): *The scope*'s last sub-bullet carries K's printed constants; new bullet *The M-factored domain (derived)*. Closing line updated. D2.7 closure l.7 and l.61 updated. Hashes: note 0af123485777… (840 lines), D2.7 closure 521570fa3327…. No review dispatched.

**Not closed.** The starting gradient and current; the deformations' current; the Landau representatives' identities; the data's 𝐉; (2.36) about 0; the complex curvature conditions (2.34), (2.35), (2.37); the choice C₀ ≥ C_KC₁ (for review).

## (R-eval): The s = 1 Points Lie in 𝓜^c (28 October, 19:29)

**The question.** The M-factored landing at s = 1 needs the T-step's point e^{iη𝐇(1,tB′)}P_{k+1}(𝐔) to lie in 𝓜^c, the complexified image of the old insertion's post-R map. The map's l.108 (ii) gives the minimiser identity only in the small-field form.

**Correction to the note.** The note wrote U^{post} with 𝐁_k(Y₁). Bałaban's old function is built on U(𝐁_k″(Y₁), M·(𝐔)) (LFR II p.375 l.14), with 𝐁_k″(Y₁) = 𝐁(Y₁) ∪ 𝐁_k″ (p.373 l.16–18, joined by CRE (2.14)). The ″-set is finer than the post-R 𝐁_k on Z, and the old function depends on the finer averages, so U^{post} is now defined with 𝐁_k″(Y₁).

**Derived.**
- The T-step's U_k is LFR II (1.35)'s new background field U_{𝐁_k}(V), with 𝐁_k from (1.33) (p.365; the effective action is rebuilt in it, p.369 l.26). RG1 (2.6) and CRE p.266 l.7 expand it as e^{iη𝐇_k(B′)}U_{k+1}.
- Nesting: a coarse minimiser is a fine minimiser of its own averages, by admissibility and VAR Theorem 1's orbit uniqueness. Bałaban prints the instances RG1 (3.3), p.270, and LFR II (1.36) at zero 𝐇-argument.
- Localization: LFR II (1.61)'s first equality, U_k^0 = U(𝐁_k″(Y₁), M·(U_k^0)), applied to the nested configuration.
- So every real post-R background field lies in 𝓜. The Landau representatives are analytic in the data and agree at real data, so the complex s = 1 point lies in 𝓜^c. Older insertions (step j < k) follow because determining sets only coarsen.

**Weak points, checked.** (1.61)'s equality is printed for U_k^0, a 𝐁_k″-configuration; it applies to U_{𝐁_k}(V) only through the nesting, which holds up to a gauge transformation. That suffices, since the words are gauge invariant and *The M-factored domain* asks only the Landau representative. "Coarser averages are iterated averages of the finer ones" is what RG1 (3.3) uses for M^j. The bounds of (iii) go through Proposition 9 for U^{post}'s own determining set, and the chain's U_k^0(M(𝐔)) already takes the ″-averages, so the change from 𝐁_k(Y₁) to 𝐁_k″(Y₁) should leave them unchanged. (iii) has not been re-read line by line for a use of the coarser data on Z.

**Note edits.** The OPEN item and the closing-line item removed. *The transport form*: U^{post} uses 𝐁_k″(Y₁). *The M-factored domain*, *At s = 1*: the derivation in five sub-bullets. Hash: note fc29afde465e… (844 lines). No review dispatched.

**Not closed.** As in the previous section.

## (R-eval): (iii) Re-Read, and the Starting Values Derived (28 October, 19:40)

**(iii) against 𝐁_k″(Y₁).** Every bound in (iii) is per fine bond or uniform in the block scale j′, and S_L already counts Z″'s layers. No step uses the coarser post-R set on Z. The change also makes U_k^0 ∘ M well defined, since (1.50) takes data on Z at the scales of 𝐁_k″; the note says so at *The transport form*.

**The single evaluation, as first stated, does not work.** Proposition 9 applied to the chain's whole complex data costs K against the room near the newest layers, which is the problem the M-factored domain removed. It is now stated as a route for the remaining items, applied only to differences from 𝐔's own part.

**The starting values (derived).** On 𝒟^{λ,M}_k take 𝐔 = P(𝐔) ∈ 𝓜^c. Then Φ(𝐔) = U_k^0(M(𝐔)), a VAR minimiser, and its complex part is 𝓗(Δd) + T₁ + T₂ relative to the real base.
- 𝓗(Δd) is 𝐔's own complex part, so its gradient and current are given by the domain's definition. This removes the old D*D-of-A′ problem and the factor K on A′.
- T₁ is the response to the complex data difference on Λ ∩ Ω″^{∼2}_{h+1}, which is O(1)B₃B₅M⁵s_Z by (1.41) and (1.45). (190)'s entries give its gradient and D*D with decay from Λ, so it is absorbed by λ := 4max(C_Λ, C_Λ′)M⁵/(1−β) on Z's layers. On the newer layers the decay gives e^{−δ₀M/(16M₁)} per layer, against M⁵, for M large.
- T₂ is the kernel shift caused by the real data difference δ^{re} on Λ. The real data differ through V_k′ = exp ig_kB′ alone, with |g_kB′| < M₀ε_k (LFR II (1.1), p.356, and the display below it), via U_0^{(AL)} of p.366 l.24 and (1.34). The Cauchy estimate in the Λ-localized direction wδ^{re} keeps (190)'s pointwise decay, so T₂ ≤ O(K²B₃M₀ε_k/r_B) times 𝐔's room, which tends to 0 with g.
- The real base U_k^0(M(U)) is taken as its Landau representative relative to U. The words are gauge invariant, so u_k″ plays no part, and the base change has coefficients O(KB₃M₀ε_k).

**Weak points, checked.**
- The bound |g_kB′| < M₀ε_k is printed for the denominator's integration variable V′ of (1.1). The numerator's V_k′ carries the same χ in (1.1), so it is read as the same restriction; χ's definition in LFR I has not been re-read.
- U_0^{(AL)} is localized to Z (U_{k,Z}^{(L)}), while the post-R configuration is global. The difference sits in Z's boundary layer, where (1.36)'s argument is at most 44d²ε_k (p.365), also g-small.
- K is uniform in M once *S_L is finite* holds, since a larger M only increases the distances, so M⁵e^{−δ₀M/(16M₁)}C_Λ′ → 0.
- λ now depends on K through C_Λ′; it is fixed after L, M, C₀, and C₁, and before g. Its consumers, D2.6's 4c_πMλα_{1,k+1} ≤ 1 and (b2)'s O(λρ_k), use only g small.

**Note edits.** OPEN heading: the deformations' current, the curvature conditions, and the data's 𝐉. The starting-values item removed from the OPEN list and the closing line, and added to the derived list. *What would close it*: the single-evaluation bullet restated as the route for the remaining items. (i): λ := 4max(C_Λ, C_Λ′)M⁵/(1−β). (iii): *The transported part and the response (OPEN)* replaced by *The starting values γ_Φ and κ_Φ (derived on 𝒟^{λ,M}_k)*. D2.7 closure l.7 and l.61 updated. Hashes: note e6ecd1b00ca5… (848 lines), D2.7 closure 6ada5ad7a21e…. No review dispatched.

**Not closed.** The deformations' current (Hessian of λ̂); the Landau representatives' identities; the data's 𝐉; (2.36) about 0; the complex curvature conditions (2.34), (2.35), (2.37); the choice C₀ ≥ C_KC₁ (for review).

## (R-eval): The Five Points Closed (28 October, 20:25)

**Status.** (R-eval) derived, not reviewed. The choice C₀ ≥ C_KC₁ stays for review. (R-round), (R-member), and (R-att-ext) stay OPEN.

**The five points.**
- The Landau representatives. REG's representative depends on the element it is normalised from (p.80 l.29–31), and REG generates it from the axial-gauge element (p.81–82, (1.28)–(1.31)). VAR's representatives 𝕎 := e^{iη𝓗(B)}U₀ take 𝓗's argument from the configuration's own plain data. 𝕌 = 𝕎^G with G = u_L followed by w: u_L by CMP98 (106) (REG p.88 l.29–30), w the data-preserving axial fixing, with w = 1 at the block points (REG (1.14)). The identity holds at real minimisers by VAR Theorem 1 and extends to 𝓜^c. The base change Θ and REG's fixed point μ are no longer used.
- The bound on G. At the block points, |λ̂(y)| ≤ 16dL^iη|A_L|_{(0)} by REG (1.70)–(1.71). D₀λ̂ = A_L − N(λ̂) gives |D₀λ̂|_{(0)} ≤ 2(|A_L| + |A_Φ|), and a path of at most dL^i bonds inside the block gives |λ̂|_{(1)} ≤ B_Gε.
- The current. J^h(V^G) = Ad_GJ^h(V) (RG1 (1.10)), so C_n − C_{n+1} = (Ad_G − 1)ΔJ + (ΔJ − ΔJ^{re}). The first term needs only |λ̂|, and the second is (190)'s D*D entry plus 𝒬's mixed difference, which is first order. No Hessian enters.
- The data's 𝐉. 𝒟^{λ,M}_k is a set of pairs (𝐔, 𝐉), and P acts on 𝐔 alone, so the pair's 𝐉 obeys 𝒟^λ_k's current condition and (2.36) by definition. The new terms take it where J_k appeared (RG1 p.275 l.3–4).
- (2.36) about 0 and (2.34), (2.35), (2.37). Quoted from LFR II (1.65) (p.375) and LFR I p.191 l.25–31 with (1.68), since 𝒟^λ_k ⊂ 𝒟_k = Ũ_k^c (SW closure (b1)).

**Weak points.**
- The reduced frame's sources are conjugated by the accumulated ũ, whose complex part grows by O(B_G)L^jηε per step. This gives a term (b) with a sum over the earlier stages, so the sum's factor is N^{2+β₀}δ′_k, not N^{1+β₀}δ′_k. It is still g_k times a power of log g_k^{−2}.
- G_n's complex part is bounded by *The bound on G* after the real gauge transformation G_n(U). The note states this in one sentence.
- 𝒬's first-order structure is my derivation: D* of a local analytic function on plaquettes is bounded by its values on the neighbouring plaquettes.
- (1.65) and LFR I's chain statement are Bałaban's claims, with the proofs omitted as "almost identical". They are applied at a G^c transform of his chain, with membership read as a condition on some representative (CRE p.261 l.60–61), as on the note's l.17.
- The path of at most dL^i bonds stays inside one layer-i block of Ω_i∖Ω_{i+1}.

**Note edits.**
- The top: (R-eval) is derived and not reviewed, and the five parts are listed with their bullets. *What would close it* is renamed *The constants*, and the single-evaluation bullet is removed. The derived list is updated.
- (iii): *One step* takes 𝕌's own data, with C_G = O(1). *The Schwarz bound* is at s̃. *The base* is trimmed, and *The Landau representatives* and *The bound on G* are rewritten. *The base change* and *The bound on u* are deleted. *The reduced frame* is moved before *One step's deviation*, which now has the terms (a), (b), and (c′). *The induction* and *The sum* are updated.
- *The gradient of the deformations* and *The current of the deformations* are separated, and the 𝐉 coordinate is marked derived. A quoted bullet on the curvature conditions is added. The M-factored domain is defined as a set of pairs. The downstream "OPEN (R-eval)" mentions now read "derived and not reviewed".
- D2.7 closure: l.5, l.7, and the status lines of items 5 and 15 and of the summary are updated.

## (R-round) and (R-att-ext): Closed (28 October, 20:52)

Both are derived and not reviewed. (R-member) is the one R-step input still OPEN.

**(R-round).** The bound of 8(105MR_k + 1) on the members in a component's slots was wrong: members made at a step j < k can have L^{k−j} disjoint intervals in one step-k bond (D2.6 closure 5.2 (T0)). The rounding is now counted per cube.
- A member is big if j = k or σ(D) ≥ 22. Then #_k(X_D) + n_k(D)/M ≤ (21/20)σ(D) and diam_∞(T_D) ≤ M(21/20)σ(D), with no 17, since 17 + σ/4 ≤ (21/20)σ and 16.1 + 0.23σ ≤ (21/20)σ once σ ≥ 22.
- A member is small if j < k and σ(D) < 22. Then #_k(X_D) < 22, so T_D lies in X^{(22)}, the set X⁺ widened by 22 layers of π_k-cubes.
- B_P uses X^{(22)} in place of X⁺⁺, and D_P uses 4R_k + 48 in place of 4R_k + 4. #π_k(X^{(22)}) ≤ (105R_k)^d for R_k ≥ 44, and the margin of (1.89) pays it.
- Every term 17#𝔅(P), every e^{2ν_r}, and every e^{85MC_jnε_k²} per member is removed from (6B) and (6C): *The count*, σ̄(g), *Cubes*, *Traversals*, *Together*, *Diameter*, *The payment*, *Spans*, *Joins*, *Join count*, *First case*, *The weights*, σ̃(D_g), *Units*, *The extent*, and the re-run of D2.7 15.7.
- (R-eval)(i) also used the member count. *The masses and weights* now counts per component: the single-loop masses e^{2ΣA} grow to at most e^{2λΣA}, and the cross carry product grows by at most exp((λ−1)Σx_D) ≤ e^{2(λ−1)A^×} (*The carried cross total*). So P := 2ΣA + 2A^×, independent of the number of insertions.

**(R-att-ext).**
- ext^{coll} is the distance from the collar Coll_k, one set for all components (D2.6 closure 5.0). D_g is counted in the species of its first att member (D2.6 closure 5.5). The distance runs through a cube y₀ of a polymer in the component, or of Y_{W₁} on span(g). This gives ext^{coll}(D_g) ≤ polymer part + max over dev members of ext(W) + max over att members of ext^{coll}(W). Each maximum is paid by its member's own extent weight.
- The att members' e^{17ν_r} enters D2.6 closure 5.0's species normalisation, as e^{c_W} does, once per insertion. It replaces A_j(Z) by e^{17ν_r}A_j(Z) ≤ 2A_j(Z), since 17ν_r ≤ log 2 under 5·2^{d+2}ν_r ≤ 1. 15.3's amplitude bound then reads c₁e^{3+4ΣA+2a_k} ≤ e^{−p₀(g_k)/2} for small g_k.

**Weak points for review.**
- The per-insertion growth factor λ in (R-eval)(i) is taken from SW closure (b2)'s linear form b_W(Dev_W + a*_W + j*_W). That an insertion meeting several components' neighbourhoods grows by λ only once rests on the growth being pointwise per bond.
- A^× is uniform in K, but it is a constant fixed by the loops (linear in 𝔞̄(ℓ₁+ℓ₂)), not a polylog. Each component's margin pays e^{2(λ−1)A^×} in full, which needs p₀(g_k) large against A^× (small g_k for fixed loops).
- In the re-run of D2.7 15.7, the small members add 44M per localisation domain to the diameter and 176M to |span(g)|. They are paid at 3ν_r/80 per unit of D_P, under R_k² ≥ 440/ν_r.
- R_k ≥ 44 is needed for (104R_k + 44)^d ≤ (105R_k)^d.
- The normalisation e^{c_W+17ν_r} is applied to every att insertion, not only to those that become members, so that the species totals are fixed before the groups are formed.

**Note edits.**
- (6B): *Lengths*, *The free decay*, *The volume*, *The count*, *Big and small members* (new), *The rounding*, σ̄(g), *Cubes*, *Traversals*, *Together*, *Diameter*, *The payment*, *Spans*, *Joins*, *Join count*, *First case*, and *The weights*.
- (6C): σ̃(D_g), *Units*, *The extent*, *The attached extent* (new), *The members' weights* (att bullet), *The payment*, the re-run of D2.7 15.7, and *The weights*' collar line.
- The top: l.3, l.15, (R-eval)(i) l.59 and *The masses and weights*, the (R-round) and (R-att-ext) blocks, and the summary line after them.
- D2.7 closure l.10.

## Reviews of (R-round) and (R-att-ext): Triage and Repairs (28 October, 21:20)

Three headless reviews (Opus 5.5, effort high, note SHA256 ec7b3e991ae2…): `two-loops-rround-units-20261028-r1`, `two-loops-rround-uses-20261028-r1`, and `two-loops-rattext-20261028-r1`. None found anything fatal.

**Outcome.** (R-round) is repaired, (R-att-ext) is reworked, and one new OPEN item, (R-eval-cr), replaces the unsupported per-component argument in (R-eval)(i). All of this is derived and not reviewed.

**Serious findings and repairs.**
- U-S1, uses-S2 (stale "+17" at l.456 and l.504, (H2) of R-made D_g^×). The segment count "4.2σ(W) + 73 ≤ 5(σ(W) + 17)" used a per-member constant that σ_g no longer has. Repair: a big cross member's segment meets ≤ 4.2σ(W) + 5 ≤ 9.2σ(W) cubes. A small cross member uses its T_W ⊆ X^{(22)} ⊆ B_P as the connector, counted once as a set. So E_D gains ≤ 10.2σ_g ≤ 29σ_g, and 419σ_g + 160 is unchanged.
- U-S2 (claim (e) overbroad). The 𝒲_g span members keep 17 each. The claim is now restricted to the slot members 𝔅(g), at l.202 and *The rounding*. The 𝒲_g constant is paid through masses: dev members in x_g, and non-dev members in the species normalisation.
- uses-S1 ((R-eval)(i): growth λ derived only for dev insertions). Accepted. The per-component argument (P := 2ΣA + 2A^×) is withdrawn.
  - The dev clause is asserted on 𝒟^λ_k (l.45).
  - D2.6's att bounds hold on the family (l.52).
  - The cross insertions' weights are OPEN (R-eval-cr): (ii^cr), (6)'s production, and the cross carry lemma are stated on 𝒟^{sub}, and composite cross bounds are products with no bound on their number of factors. The closing route is written in the block: (ii^cr) on 𝒟^λ_k through (S-w)'s vertex sups and transports.
- att-S1 (collar across steps). Accepted: 5.0 measures from Coll_{j(W)}, and an R-step can remove the collar cubes around a first-class component. Repair: the members enter through their domains (ext(W) for dev, diam T_W for non-dev), not through their collars.
  - Case (a): D_g's Y-set meets the post-R Coll_k, and ext^{coll}_k(D_g) ≤ Δ_g.
  - Case (b): otherwise D_g continues the lineage of its first non-dev member W₁ from Coll_{j₁}, with growth ≤ e^{−p₀/4} ≤ δ_k at the R-step.
- att-S2 (cases missing: att by box with all members dev; wrap and lw members). Case (a) covers the box alternatives. lw members are treated as att, by 5.0's "the same for … lw(Z)". A D_g with a wrap member is wrap(k) by map l.285's rule, and its mass is in (ii)'s wrap sums.
- att-S3 (species assignment). Fixed by case (a) (att(k, ·), charged as 15.6(e)) and case (b) (W₁'s lineage).

**Minor findings and repairs.**
- The (5/2)ν_r rate on X^{(22)} is computed (5p₀/64), and the margin bullet now says X^{(22)} in place of X⁺.
- p.389 l.27–28 is cited for the per-X′_r payment, and *The free decay*'s reference now points to *Cubes*.
- "Descendants" now reads "untouched continuations", and T-step products of every species, lw and wrap included, have u = 1.
- The multiplicity in X_{D_g} applies to the 𝒲_g domains only. ∪dom P is counted as a set.
- Attached insertions (15.5(i)) are not members of 𝔅(P). Their constant 3 is paid through their masses in a_k(X).
- The linear factor of 15.7 has base ≥ 4MR_k, so it needs R_k² ≥ 880/ν_r for small g_k.
- The doubling of A_j(Z) is replayed through D2.6 7.1–7.3: ε_A at most doubles, and the comparisons hold for small g_*. ΣA now denotes the A′_j totals.
- σ̃ takes ½σ(W) + 17 per member, so that the other half pays the non-dev extent term. u = 21/10 when no slot holds a carried insertion.
- The packet's line citation for *The carried cross total* was off by eight lines. No change to the note is needed.

**Weak points for the next review.**
- Case (b)'s growth bound: D_g adds ≤ e^{−p₀(g_k)/4}w(W₁), which rests on B(g)'s polymer amplitude and the other members being paid in their own registers.
- Wrap members: B(g) times the other members' factors ≤ 1 for small g_k, so w̄ at most doubles.
- The non-dev member's dependence set is taken as its Cov domain, inside T_W.

**Note edits.** l.3, l.5, l.59, *The masses and weights* and *The payment* in (R-eval)(i), the new (R-eval-cr) block, the (R-round) and (R-att-ext) blocks, l.222, (6A)(i)'s (H2) for R-made insertions and *The share of D*'s segment count, *The free decay*, *The volume*, the margin bullet, the 𝔅(P) definition, the factor list, *The rounding*, X_{D_g}, σ̃(D_g), *Units*, *The extent*, *The attached extent*, *The members' weights*, and the 15.7 linear factor. D2.7 closure l.5.

## (R-eval-cr): Derived on the Dilated Sub-Domains (2 November, 23:32)

The cross clause (ii^cr) is now stated with sup bounds on 𝒟^λ_k, M-factored, as the dev clause and D2.6's att bounds already were. A composite R-made cross insertion's constituents are then each bounded at Φ(𝐔) by their own clause, so no factor per constituent arises.

**Premises checked against the text.**
- Map l.1407: the transport bound on Ω_{k+1}, under c_πα_{1,k+1}M ≤ ν/64.
- Map l.1496 and l.1498: the per-slot condition 20c_πM‖a′‖_∞ ≤ 1, implied by (12)(d)'s c_πα_{1,k+1}·41M/L ≤ ν_r/16, and the a′-cost e^{(ν_r/16)σ_k(W)} per touched W.
- Map l.1571–1577: (S-w)'s right side, the KP condition ε̄^{old} + ε̄^{ref,k} ≤ ε_*/2, and ε^{new,β} ≤ K_β(b_k/ᾱ_k)ε^{old}.
- SW §3(b1): 𝒟^{sub}_1 = 𝒟_1 (one layer).
- The note's l.40–57: the family's definition, the transfer under (b3)–(b4), (b2)'s size O(λρ_k), §5.4's condition 4c_πMλα ≤ 1, and the landing of Φ(𝐔).
- The note's l.417: a group with a non-dev parent takes the first parent species, so a cross(k+1) group's old members are dev.
- D2.6 triage R23 m-3: c̄_* = max(2K_β, C″).

**The derivation.**
- Production: on Ω_k∖Ω_{k+1} the phase room is min(λ, c′) times 𝒟^{sub}'s, so the transport conditions hold with c′α_{1,k+1}. The dev vertex sups grow by at most λ, so (S-w)'s right side grows by at most λ², which gives C_cr^λ = λ²C_cr.
- Carry: 5.1 runs on the family through the l.46 transfer, and 5.4 runs under §5.4's family condition. c̄ is unchanged.
- R-steps: Φ(𝐔) lands in 𝒟^λ_k on 𝓜^c, and reaches the rest through P. This covers 15.6(c)'s B(g), the second case's w_{k−1}(W), and 15.8's third class.

**Weak points for the review.**
- The λ² bound on (S-w)'s right side: the old sums enter only linearly and quadratically.
- Whether c̄ depends on the other vertices' sizes beyond the KP condition.
- The transports on Ω_k∖Ω_{k+1} at production: the old layer is covered by the top-layer bound, times c′.

**Note edits.** l.3, l.5, l.59, l.64, the (R-eval-cr) block (rewritten in place), (ii^cr)'s w(W), C_cr at the end of *Production*, the cross carry lemma's domain and its 5.1 and 5.4 steps, the cross-member bullet of 15.5 (l.568), *The rooted sum*'s cross-member bullet, 15.8's third class, l.230, and the (8.2) header.

## (R-eval-cr) P1: Triage (2 November)

Referee log: `Balaban\reviews\work\referee_cli_20261102-233323_scope_twoloops_P1_Revalcr.json`. Findings: 2 ERROR, 5 MINOR.

- **P1-1 (ERROR), accepted, repaired.** After an R-step the cross clause is derived only at the next T-step's evaluation points. The note now defines it as the sup over 𝒟^{ev}_k after the R-step at k, and over 𝒟^λ_k before it. Edited: *How it holds*, the R-step bullet, and (ii^cr)'s w(W).
- **P1-2 (ERROR), accepted as a defect of the text, closed.** The finding's premise, that a second-class Y_i lies on older post-R layers, is false. The new determining set puts all of Z on the top layer: Γ_k = Γ″_k ∪ Z^{(k)} (LFR II (1.33), p.365 l.3–8), and Γ_k = Ω_k^{(k)} (CRE (2.2), p.255 l.16–17). A second-class component carries the scale-k large-field function χ^c_k(Y_i^{∼−6}) inside the new Ω_k (p.379 l.18). So s_Z ≤ α_{1,k}L^{−k} holds on both classes, and the landing is class-independent. This matches Bałaban's top-layer radius at both classes (p.366 l.24–28, p.379 l.28–32). The defect was the note's own sentence "After R the first-class components lie in the new Ω_k", which restricted the landing. Repaired in *Where it lands* (l.39), the R-step bullets of (R-eval-cr), 15.8's third class, l.3, l.259, and the (8.2) header. An OPEN block (R-eval-2nd), written briefly on this misreading, was removed.
- **P1-3 (MINOR), accepted, repaired.** The λ-version of the a′-transport condition, c_πλα_{1,n+1}·41M/L ≤ ν_r/16, is now stated in the carry bullet and in the constants line.
- **P1-4 (MINOR), accepted, repaired.** 5.1 now cites the s ≠ 1 route through P ((iii) l.114–116).
- **P1-5 (MINOR), accepted, repaired.** l.14 and the D(k)(iii) sentence near l.852 now separate D(k)(iii)'s 𝒟^{sub} clause from the class's 𝒟^λ clause.
- **P1-6 (MINOR), accepted, repaired.** The (8.2) header lists (R-eval), (R-eval-cr), (R-member), (R-round), and (R-att-ext) as derived and not reviewed, and (R-eval-2nd) as OPEN.
- **P1-7 (MINOR), accepted, repaired.** c′ depends on β, L, and β₀.
- Found while repairing: inserting (R-member)'s span class first in 15.8 shifted the ordinals ("four classes", "the third class"). The span class is now the fifth, and the list says five classes.

## (R-eval) Packet A (the Landing), Round A1: Triage (3 November)

Referee log: `Balaban\reviews\work\referee_cli_20261103-001452_scope_twoloops_RevalA1.json`. Findings: 2 ERROR, 7 MINOR. The referee confirmed the P1-2 repair ((1.33) with CRE (2.2)).

- **A1-1 (ERROR), accepted, repaired.** The per-fine-bond response bound was labelled "quoted", but no cited line prints it, and (1.45) is uniform in j, so it loses L^{k−j} per fine bond on Λ's older scales. The note's *The response is sourced on Λ* now derives it in four steps.
  - (a) The scale-k response: (1.41) (p.367 l.16–18) bounds B′_Λ as a scale-k block field (V_Λ lives on Z^{(k)}, p.365 l.14), with |B̃′| ≤ O(1)L^ks_Z.
  - (b) The fine field: VAR (190) (p.308 l.38–45) at j = j′ = k gives C_{rsp}M⁵s_Ze^{−δ₀d/16}.
  - (c) The averages: the j-averages on Λ ∩ Ω″^{∼2}_{h+1} cost O(1)L^j.
  - (d) Across the layers: (190) with PRT2 (2.46)'s layer-local distance, and the separation of consecutive layers by M-cubes (LFR I p.179 l.20–25) or MR_j-cubes (p.179 l.9, l.28). This gives L^{j′−i}e^{−δ₀d/16} ≤ L once Le^{−δ₀M/16} ≤ 1.
  - Result: C_Λ = O(1)L(C_{rsp} + M^{−5}) and δ = δ₀/32. New condition: Le^{−δ₀M/16} ≤ 1, M large given L.
- **A1-2 (ERROR), accepted, repaired.** D2.6 §5.4's factor runs over the carry length. The note's att sub-bullet now has three parts.
  - Production at step j on 𝒟^λ_j: c_πλα_{1,j}M ≤ ν/64 and c_πλα_{1,j}·41M/L ≤ ν_r/16, with the production constants multiplied by λ².
  - The carry over the carry length k + 1 − j: the ratio of the family rooms is at most ((1−β)/2)^{k+1−j}, on every layer, by min(λ, c′^{k+1−n}) ≤ c′^{k+1−j}min(λ, c′^{j−n}).
  - D2.6 §5.1 on the family.
- **A1-3 (MINOR), repaired.** c′ > 1, that is, L > 2(1+β₀)/(1−β).
- **A1-4 (MINOR), repaired.** The transported part includes the 𝐇-part. The pre-R budget ((7/8)(1−β)λ^{(k)}_n + β/2)α_{1,k}L^{−k} needs β ≤ 1/5 (CRE's β = 1/8).
- **A1-5 (MINOR), repaired.** The transport form is stated through P: Φ(P(U)) = U_k^0(M(U)) at every real U, the bounds are taken at Φ∘P, and the later sources are conjugated.
- **A1-6 (MINOR), repaired.** LFR I's preliminary integrations also move bonds only to newer layers ((1.12)–(1.15), p.179 l.33–p.180 l.22). So the original layering, 𝐁″_k, and 𝐁_k are ordered from older to newer at every bond.
- **A1-7 (MINOR), repaired.** T_Y is unchanged by the Λ-response; it is still reduced by 4K.
- **A1-8 (MINOR), repaired.** Two consumers are added.
  - (6c)'s covariance-note inputs: that note reads W only on X_W ⊂ Ω_{k+1} (its §0, l.20, l.26–29), where λ^{(k+1)}_{k+1} = 1. So R-av's top-layer form and c_πα_{1,j}·4096M ≤ ν are used as stated, with no factor λ.
  - The c₀-rotation charge (map l.1498): |log c₀| ≤ λC_{c₀}α_{1,k}L^{j−k}, so the map's condition holds for g_K small given λ. At j = 0, λ^{(k)}_0 ≤ c′^k and Σk^{1/2}2^{−k} < 1.35 give ρ_ω with 4C_{c₀} in place of 2C_{c₀}, and the O4 note's C_ω with C_w + 3d + 4C_{c₀}. The result is free of λ.
- **A1-9 (MINOR), repaired.** SW l.93, and p.375 l.25–28 at l.36.

## (R-eval) Packet A (the Landing), Round A2: Triage (3 November)

Referee log: `Balaban\reviews\work\referee_cli_20261103-005245_scope_twoloops_RevalA2.json` (00:52–01:15). Findings: no ERROR, 4 MINOR. A1-1 to A1-9 are confirmed closed, except the part of A1-5 that is A2-1.

- **A2-1 (MINOR), accepted, repaired.** l.37 said U = U^{post}(M(U)) for every real post-R configuration, and implied Φ(U) = U_k^0(M(U)) at gauge transforms of minimisers. Both statements are now restricted to 𝓜 := {U real : U = P(U)}. At U = V^g with V ∈ 𝓜, P(U) = V^{g̃}, so Φ(U) = U_k^0(M(U))·(V^{g̃})^{−1}V^g. The bounds are at Φ ∘ P, which is unchanged.
- **A2-2 (MINOR), accepted, repaired.** Step 2's response to B̃′ is now bounded: (190) at j = j′ = k gives O(1)L^{−k}sup|B̃′| ≤ O(1)s_Z. Step 3's +1 covers it together with 𝐔's own phase.
- **A2-3 (MINOR), accepted, repaired.** On the family the old masses grow by up to λ². Three conditions are now stated with λ²ε^{old}: (S-w)'s condition (map l.1571), (12)(e)'s window counts, and D2.6's (T0), (163 + C_win)M(ε^{new} + ε^{old} + ε^{ref}) ≤ ν_r/8 (D2.6 l.89). All three hold for g_K small given λ, by ε̄^{old} + ε̄^{ref,k} ≤ 2L⁴C(M/ν_e²)C^{(k)}ρ_k·pl_k (map l.1580).
- **A2-4 (MINOR), rejected as stated: the referee read the raw files.** The convention is the `pNNN_corrected.tex` file lines (memory rule; the table's convention). The raw files carry an extra `\pagemark` line, so their lines are one higher. In the corrected files VAR's B₃ sentence is at p.279 l.28, and LFR I p.191's statement is at l.39–41, with the left factor at l.40. Both pins stand.
  - The finding exposed a real defect: packet A's other pins were raw-file lines. All twenty are converted to corrected lines (p.365 l.2–7 and l.13; p.366 l.23–27 and l.28–32; p.367 l.15–17, l.19–23, and l.40–45; p.370 l.3–8; p.373 l.15–17; p.375 l.24–27; p.379 l.17; LFR I p.181 l.40, p.192 l.43, p.200 l.12–19, l.20, and l.30–31, p.179 l.19–24; CRE p.255 l.15–16; VAR p.308 l.37–44; PRT2 p.231 l.11), each matched by content.
  - The other packets' pins are converted when each packet is prepared. The table's §11 bullet with CRE p.255 and LFR II p.365 is converted through the table protocol.
- **The referee's "not checked" items, now checked.**
  - VAR (190)'s d is PRT2's distance: VAR p.288 l.46 takes d(y, y′) from its [3], which is PRT2 (VAR p.309 l.24).
  - LFR II's [10] is PRT1 (LFR II p.392 l.24).
  - Both pins are added to the note.
- **Status:** packet A has no ERROR in A2, but A2-2 and A2-3 are gaps in the mathematics, not wording slips. Round A3 follows.

## (R-member): Derived (2 November)

Formerly OPEN. It is now derived and not reviewed: the merge rule D_G for cross members shared between groups.

**The derivation.**
- Sharings: W ∈ 𝒲_g ∩ 𝒲_{g′} or W ∈ 𝒲_g ∩ 𝔅(h). Single-loop insertions belong to one group, a cross insertion is a slot member of at most one polymer, and cross groups have no span members.
- Rule: the components of the link graph that contain a cross insertion become one D_G each. The identity holds because D2.7 15.6(f) is linear in each interval factor.
- Bound: ‖D_G‖ ≤ ∏B(g)∏‖W‖ in the projective norm. Its species is cross, in M^cr, in W₁'s lineage, at u = 19.
- Count: E ≤ 1696σ + 160. The share condition is (220432ν_f + 1672ν_e)/L ≤ ν_r/4, so L₀^× = 10⁶ (0.235). (T0) holds at u = 19 with (3230 + 70756/c_w).
- Weights: a cross member's ε_k splits into ε_k/2 (Ψ), ε_k/4 (joins and links), and ε_k/4 (the linear factor). The links cost C_lk := 2max(C_gr, C_jn), under 100MC_lkε_k ≤ ν_r. The lineage growth is C_y := 77MC_lk/(eν_r).

**Weak points for the review.**
- The completeness of the sharing list (whether a cross insertion can be a member of two polymers' slots after R).
- The units count u = 19 and the 18.05σ per cross member.
- The ε_k split against (6B)'s Ψ payment and the join count.

**Note edits.** The (R-member) block, l.264, the constants list, L₀^× at l.521 and l.806, the factors list, *The units of the members*, *The arc set*, the D_g sentence (l.662), the join count, the hard core, C_y (l.719), the 15.8 classes, (6C) l.789–792, and the cross carry's (T0) positions.

## (R-eval) Packet A (the Landing), Round A3: Triage (3 November)

Referee A3 (`referee_cli_20261103-012309_scope_twoloops_RevalA3.json`): no ERROR, four MINOR. A2-1 to A2-3 are confirmed closed, A2-4's rejection is confirmed, and the twenty converted and three added pins match. Not clean, so A4 follows.

- **A3-1 (l.58), repaired.** "(S-w)'s right side is at most λ² times its 𝒟^{sub} value" was false for map l.1574's quadratic term, and a literal λ² per production would compound through the att masses. Now the right side is written out; the source term gains λ²; map l.1581's recursion runs on the family with 2λ²C_winC_M, the carry term unchanged and the (β) and quadratic terms gaining at most λ² and λ⁴, still within map l.1582's bounds for g_K small given λ. So C^{(k)} stays at most λ² times its 𝒟^{sub} bound, uniformly in k.
- **A3-2 (l.43), repaired.** (a) PRT1's (1.67) and its γ₀ "dependent on d only" are at p.29 l.27–30, not p.28. (b) C_Λ contains M^{−5}; it is now "bounded, uniformly in M ≥ 1, by a constant depending on d and L only". The table row l.128 follows (peer protocol).
- **A3-3 (l.42), repaired.** The layer separation now rests on {Ω″_j} being admissible (LFR I p.179 l.40), read with l.20–22's "Thus … separated by one layer of M-cubes", which covers the layers in Z and outside it.
- **A3-4 (l.56), repaired.** The data transfer now points to the bullet on data in 𝒟^λ_{k+1} (l.51).
- **Not checked by A3, now checked.** VAR's δ₀ and B₀ are PBG Theorem 3.12's common rate and constant (VAR p.285 l.25, "Theorem 3.12 from [5]"; VAR's [5] is PBG, p.309 l.24), "a positive, absolute constant depending on d and L only" (PBG p.423 l.39–p.424 l.3). The note's l.118 pinned PBG Theorem 3.1 (p.397 l.37) instead and now cites p.423–424; A4's scope lists these pages.

## (R-eval) Packet A (the Landing), Round A4: Triage (3 November)

Referee A4 (`referee_cli_20261103-014738_scope_twoloops_RevalA4.json`): no ERROR, three MINOR. A3-1 to A3-4 are confirmed closed, and so are A1-1 to A1-9 and A2-1 to A2-3; A2-4's rejection stands. Not clean, so A5 follows.

- **A4-1 (l.38–44), repaired.** The response bound left out a first-order term. Since E(U) ≠ 1, the shared complex change Δd of the data passes through two minimisers whose real Λ-data differ by δ^{re}. Steps 1–4 bound only T₁, the response to the complex Λ-data difference.
  - The new bullet *The mixed term* bounds T₂ := ∫₀¹[κ(tΔd ⊕ δ^{re}) − κ(tΔd)]Δd dt, the same T₂ as (iii), *The starting values*.
  - The bound is a Cauchy estimate in w on VAR's ball r_B = 2C₁ε₁, which is independent of g. It uses |δ^{re}| ≤ O(B₃M₀ε_k), with M₀ = O(1)B₅M⁶ (LFR II p.356 l.37, p.378).
  - Δd lies within half the ball for g small given λ: a j′-average's phase is O(1)L^{j′}λα_{1,k}L^{−k}.
  - Summing over the source layers with step 4's crossing argument, in both directions and with the rooms' ratio c′^{i−n′} for older sources, gives at most C_{mx}ε_kλ^{(k)}_iα_{1,k}L^{−k}, where C_{mx} := O(1)LB₃M₀/r_B.
  - (190)'s uniformity on the ball also covers the mean-value steps at complex intermediate data, which was A4's "not checked" item.
  - The landing (l.64–66) now takes λ := 8max(C_Λ, C_Λ′)M⁵/(1−β). Each of C_ΛM⁵ (respectively C_ΛM⁵e^{−4δM}) and C_{mx}ε_kλ^{(k)}_n takes ⅛(1−β)λ^{(k)}_n, so the response still takes ¼(1−β)λ^{(k)}_n and the landing sum is unchanged. The added condition C_{mx}ε_k ≤ ⅛(1−β) holds for g small given M.
  - l.158's λ ≥ 4C_Λ′M⁵/(1−β) still holds.
  - l.68's "response constant is 1 off Λ's decay range" now reads that the response there is at most C_{mx}ε_k times the room.
  - The table's row 128 records C_{mx} and the new λ (SHA 67d2140f72cd; the peer was told).
- **A4-2 (l.44, l.120), repaired.** "Theorem 3.12 from [5]" is at p285_corrected.tex l.25, which was checked. Both note lines and the two triage lines now cite l.25.
- **A4-3 (l.59), repaired.** The map l.1577 quote now reads C_Mρ_{k+1}·pl, as printed (checked).
- **Line shift.** The new bullet moves every note line after l.42 by +1. The ready scopes (B1, C1-1, C2a1, C2b1, Rround2a, Rround2b, Rattext2, P2_Revalcr, P1_Rmember) are shifted before each launch.

## (R-eval) Packet A (the Landing), Round A5: Triage (3 November)

Referee A5 (`referee_cli_20261103-021254_scope_twoloops_RevalA5.json`, run 02:12–02:30): no ERROR, three MINOR. A4-1's mechanism is confirmed (the Cauchy step, the two-direction layer sum, C_{mx}'s order, and the ⅛ + ⅛ landing split), and A4-2 and A4-3 are confirmed closed. Earlier rounds stay closed. A5 dropped the T₁ + T₂ commutator terms as absorbed by C_{mx}'s O(1); that is accepted.

- **A5-1 (l.40, l.45, l.158 in the post-A4 numbering), confirmed: a real gap, now recorded as open.**
  - Checked against the sources: LFR II (1.50) (p.370 l.4) gives U_k″ the data V″ on (Ω″^{∼2}_{h+1})^c. On Λ^{old} := Λ∖Ω″^{∼2}_{h+1} these V″ are T′_k(X)'s integration variables V_h (p.378 l.31; LFR I p.200 l.53).
  - LFR I p.196 l.45–46 says χ_{k,Λ} and χ′ "do not give restrictions on the variables V″ = V_h on Z′^∼_h∖Z_h". The restriction added there is χ_{h,1/2} of (1.88) (p.197 l.46–48), a curvature condition on (1, V_h). T_h acts on Z_h.
  - So the real data difference of the two minimisers on Λ^{old} is V_h against U's averages, which no printed bound controls. The note's l.158 ("agree off Λ ∩ Ω″^{∼2}_{h+1}") was wrong; l.40 and l.41 were right.
  - Two closures were tried and neither works:
    - A Cauchy estimate in w needs |δ^{re}| ≪ r_B on Λ^{old}, up to a G-valued gauge trivial off Λ. Curvature conditions give local closeness in local gauges only. A global gauge accumulates along Λ^{old}, whose extent in h-units is up to L^N times a scale-k length.
    - A locality bound on the response in the real data, via single-block Cauchy estimates and the geometric mean of the two (190) bounds, gives Λ-decay e^{−δ₀(d(x,Λ)+d(x,y′))/16}. But near Λ the bonds outside Z carry rooms up to λ, so the term stays proportional to λ and the choice of λ cannot absorb it.
  - The note now carries **Open (R-eval-old)** at its top (l.5), with what is missing and what would close it. (R-eval)'s status line, the response bullet (l.40), *The mixed term* (now T₂ sourced on Λ ∩ Ω″^{∼2}_{h+1} only), the closing bound (l.46), *The two minimisers* (l.158), the list item l.21, and the table row 128 all say so.
  - Bałaban's own chain was checked as a third route (LFR II (1.53)–(1.58), p.370–371; (1.61)–(1.63), p.373–374; p.375 l.1–13). It does not close the gap. The cut-off U_{1,2} of (1.53) keeps V″ on (Ω″^{∼2}_{h+1})^c through U_2, and it equals U_1 only on Z^c (p.370 l.14–15, p.371 l.26–27). On Λ^∼ the extended U_k^0 has "the properties of the configuration U_k″" (p.375 l.13–14). (1.65) lands in LFR I's spaces (1.64)–(1.69), whose old-layer phase radius α_{1,m}(L^mη)^{−1} (p.190 l.27) exceeds the top layer's by L^{k−m}α_{1,m}/α_{1,k}. 𝒟^λ_k caps this at λ, and the cap is used by the family's uniform bounds (the masses, (b2), the c₀ charge, and the carry), so (1.65) gives no landing in 𝒟^λ_k on Λ^{old}. The Open block (l.5) now says this; there is no line shift.
  - The open part was propagated to every later use of the landing, in place, with no line shift: packet B (i) (l.78: its status, the landing "up to T₂^{old}", and T₂ restricted to Λ ∩ Ω″^{∼2}_{h+1}), C1's ε_Φ (l.123), C2b's *Landing* (l.166), (R-eval-cr)'s *How it holds* (l.222), and (6C)'s W-sup (l.785).
- **A5-2 (l.94 *The printed inputs*, l.45, table row 128), repaired.** VAR (172) (p.305 l.31–33) assumes |V′ − 1| < C₁ε₁ and infers |B′| < 2C₁ε₁. The B-ball is now r_B := C₁ε₁/2: for |B| < C₁ε₁/2 ≤ log 2, |e^{iB} − 1| ≤ |B|e^{|B|} < C₁ε₁. Only constants change.
- **A5-3 (l.59), repaired.** l.59 now runs covariance note §4's recursion C^{(k+1)} ≤ (1+Ĉ)max_jN^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)} on the family, checked against covariance note l.139–157 and map l.1578–1582.
  - N^{(j)} gains λ² in its source and at most λ⁴ in s_j.
  - The carry term and Ĉ are unchanged: Ĉ's inputs are top-layer.
  - C^{(k)} ≤ λ²C_S′ once (1+Ĉ)λ⁴s̄ ≤ 1/4, for g_K small given λ. The three inequalities are written out.
- **Line shift.** Two lines at the top (the Open item) and six at l.59 (A5-3's sub-bullets) move the note's lines by +2 for l.5–59 and +8 after them. All thirteen ready scopes were shifted by a checked script; each replaced string occurred exactly once, and the anchors were re-read. Packet A is now l.38–76, B l.77–89, C1 l.90–121, C2a l.122–139, C2b l.140–166, E1 l.167–172 and l.213–218, E2a l.173–191, E2b l.192–212, and D l.13–37.
- **Table.** Row 128: r_B = C₁ε₁/2, C_{mx} restricted to Λ ∩ Ω″^{∼2}_{h+1}, the open part noted, and new line refs. Row 129 (C_{gr}, C_{jn}, C_{lk}, C_y, y^R_k): new line refs. SHA fb2af329a17f; the peer was told.

## (R-eval) Packet A (the Landing), Round A6: Triage (3 November)

Referee A6 (`referee_cli_20261103-030441_scope_twoloops_RevalA6.json`, run 03:04–03:21): no ERROR, five MINOR. A5-2 and A5-3 are confirmed closed. l.5 states Open (R-eval-old) correctly against all seven cited locations. The rest of the packet checks out. All five findings were checked against the sources, are accepted, and are repaired in place, with no line shift.

- **A6-1 (l.38, l.72–76), repaired.** The landing bullet dropped the T₂^{old} exception that l.46 attaches. l.72's title, l.73, l.74, and both claims in l.76 (the landing and the bound off Λ's decay range) now say "apart from T₂^{old}" or "up to T₂^{old}". l.38 now reads "derived or quoted, except for T₂^{old}".
- **A6-2 (l.61, l.66), repaired, together with the covariance note, the map, and SW.** The recursion's max_{j≤k+1}N^{(j)} contains N^{(1)} = C^{(1)}, so (1+Ĉ)C^{(1)} must fit under C_S′. Now C_S′ := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M). With it, the j = 1 case gives C_S′/2 + C_S′/8 and the j ≥ 2 case gives C_S′/4 + C_S′/4 + C_S′/8, so the total is at most 5C_S′/8 either way.
  - The same change was made in covariance note l.153–155 (the j = 1 term is now written out, and l.160 says "in either case"), map l.168, l.1580, and l.1582, and SW l.103. The peer was told before the map and SW edits.
  - The note's l.66 now handles the j = 1 term on the family (λ²C^{(1)}·(1+Ĉ) ≤ λ²C_S′/2) and states the total of 5λ²C_S′/8.
- **A6-3 (l.62), repaired.** N^{(j)} ≤ 2C_winC_M + s_{j−1}C^{(j−1)} for j ≥ 2, as in covariance note l.131 and map l.1581, so the check no longer assumes its conclusion.
- **A6-4 (l.59, l.153–155), repaired.** The internal pins are now l.54 (data in 𝒟^λ_{k+1}) and l.53 (𝒟^λ_k ⊂ 𝒟_k).
- **A6-5 (l.45, l.94, table row 128), repaired.** "ε₁ sufficiently small" is at VAR p.305 l.36. r_B is now C₁^{VAR}ε₁/2, and l.94 says that C₁^{VAR} is VAR's absolute constant (p.305 l.44), not CRE's C₁. The table row 128 says the same; SHA 0805b9a1442f, and the peer was told.
- **Outside the packet, also repaired.** l.128 PBG pin p.309 l.25. l.161 (C2b): U_k^0(M(U)) = e^{iηR₀}U holds only apart from the Λ^{old} real data difference (Open). l.162: the decomposition now names T₂^{old}. l.78 (B) had already been restricted to T₂ on Λ ∩ Ω″^{∼2}_{h+1} before A6 read it.
- **Not checked by A6:** map l.963, map (6)(e), CRE's β = 1/8, CRE's admissibility, and Ω_{k+1} ⊂ Ω_j across R-steps. CRE's β = 1/8 is recorded as checked in the table (row 93, LF *The choice β = 1/8, checked*). The map lines were reviewed with the map. Admissibility and the inclusion across R-steps go into the A7 scope.
- Packet A still cannot be clean while Open (R-eval-old) stands. A7 is held until the gap is closed; the linear order moves to packet B.

## (R-eval) Packet B (the Other Bounds and Analyticity), Round B1: Triage (3 November)

Referee B1 (`referee_cli_20261103-032508_scope_twoloops_RevalB1.json`, run 03:25–03:42): one ERROR and three MINOR. The payment arithmetic (l.84, l.820), A_k's bound, the T₂ bound, and every Bałaban pin in the packet checked out. All four findings were checked against the sources and accepted. The note was edited in place, with no line shift (948 lines).

- **B1-1 (ERROR), not closed: new Open (R-eval-curv), stated at the top of the note (l.6).**
  - 𝒟^λ_k ⊂ 𝒟_k contains CRE (2.34)–(2.37) at the configuration (CRE p.261 l.5–24). The class's bounds are taken at the reduced representative 𝕌̃, a G^c transform of the u-free representative, where only the phase, gradient, and current are derived. Bałaban's chain gives the curvature conditions at the u-free representative only, with no margin, and the spaces are G-invariant only (p.261 l.42–43).
  - A further point, from checking the sources: LFR I (1.68) prints c = 3 on Ω_k (p.191 l.12–13). The note reads p.191 l.33–34's "coincides with Ũ_k^c" (l.157). This is now said in the Open block.
  - Derived toward a repair: (2.34) at 𝕌̃ follows with C₀ ≥ 8C₁ if the real base U_r has curvature at most ¼f_nα_{0,n}ξ²(L^nξ)^{−2} on every layer. This uses 𝒟^λ_k's gradient condition, λ^{(k)}_nα_{1,k}L^{n−k} ≤ α_{1,n}, and q₀ = q₁. (2.35)–(2.37) need the same margin for U_r's current, for U_{p,X}(M(U_r)), and for their currents, plus a multi-layer form of R-av.
  - Checked and not sufficient:
    - VAR Theorem 1 has one ε₁ for all layers (p.278–279), and ε_k/α_{0,n} grows like g_k/g_n on very old layers.
    - LFR II p.361 l.17–19 (VAR (2) with O(1)B₃²B₅M⁵ε_k on Ω_k^c ∩ Ω″^∼_{h+1}), p.362 l.1–2 ((1.96) [IV] on (Ω″^∼_{h+1})^c ∩ Ω_h), and CRE p.268 l.38 (the top layer) cover only the layers within N ≤ R_k scales of the top. There ε_k ≤ (1+β₀)ε_n for g small, by CRE (2.6).
    - LFR I (1.44)–(1.52) give the layer-wise ε-regularity of the real stages U^{(n)}_{k,Z}, through χ_k^{(n)} (1.24), on Z's layers only. (1.22) covers only Ω_h∖Ω_{h+1} at n = 0.
    - Slack in Bałaban's n = 0 space: (1.50) uses all of the step's slack at α = 1/8, and the complex chain's proof is not printed.
  - A possible route, in the Open block: telescope the background over steps j = n, …, k − 1, from CRE p.268 l.38 at step n, using U_{j+1} = U_j(V^{(j)}) and |V′_j − 1| < O(1)ε_j on Ω_{j+1} (CRE (3.10), p.266; p.267 l.27), with VAR (190)'s decay. This still needs control across the earlier R-operations, whose data changes on Z exceed VAR's ball.
  - Propagated: l.7 (the (R-eval) header), l.12, l.38, l.78 (status and landing), l.80, l.113 (the identity theorem), l.158, l.213, l.222, and l.785.
- **B1-2 (MINOR), repaired.** l.78's region sentence now reads "the Λ-response, apart from T₂^{old}, exceeds …", and l.80 now carries both exceptions.
- **B1-3 (MINOR), repaired.** The sentence "the deformations are not new to R" was replaced by (iii)'s bound ⅛(1−β)α_{1,k}L^{−k} on every layer and the pre-R budget of *The R-step lands in the family*, which counts the deformations.
- **B1-4 (MINOR), repaired.**
  - l.86 now states (1.60)'s scope: X not contained in □^{∼2}, and the second group's boundary terms (p.372 l.21–22). The terms with X ⊂ Z^c and X ⊂ □^{∼2} (l.2–4) take (1.59). It quotes p.372 l.33–34 and registers the membership exp iη𝐇_k″(g_kB)U_k^0 ∈ Ũ^{(N)c} as the reading *R-chain-start*, now the third reading on l.17.
  - l.87 now calls Ũ_k^c(X, α̃₀, α̃₁) CRE's space for the 𝐁-terms ((2.41)(ii), p.261 l.59–60), and the old terms' space RG I's U^c_j (CRE p.259 l.41–42).
- **Outside the packet.**
  - l.819: the Π′ pin is now p.383 l.40 and l.44. The small-domain-branch identification is now marked as a reading, *R-Yi-branch*, with the print's two phrases (p.383 l.44 and p.385 l.45, against p.378 l.22–24). It goes into the pre-check of l.819's packet.
  - D2.7 item 5(b) and l.36 (e^{A_k} not named in sup‖w_X‖ ≤ e^{2ΣA}): l.36 lists 15.6(c)'s B(g) "through e^{2ΣA} and e^{A_k}", so whether 5(b)'s w_X includes the transports needs D2.7's text. This goes into packet D's pre-check, not edited blind.
- **Not checked by B1:** that the region near Λ stays inside X^∼, (1.65) per component (l.88), and α̃ against 𝒟_k's radii. The last is now part of Open (R-eval-curv).
- Packet B cannot be clean while (R-eval-curv) stands, so B2 is held. (R-eval-curv) is also rooted in C1 (l.110–113) and C2b (l.155–158).

## (R-eval) Packet C1 (the Deformations to One Step's Deviation), Round C1-1: Triage (3 November)

Referee C1-1 (`referee_cli_20261103-041218_scope_twoloops_RevalC11.json`, run 04:12–04:36): no ERROR and six MINOR. VAR's inputs, the Schwarz bound in s, S_L, the gauge representatives, the bound on G, the reduced frame's identity-theorem argument, and (a), (b), and (c′) checked out against the pages. All six findings were checked against the sources and accepted. The note was edited in place, with no line shift (948 lines).

- **C1-1.1, repaired (status marks).** ε_Φ's bound holds only up to T₂^{old} (l.123). l.90's header now says so for every use of ε's smallness from *One step* on. l.113 now carries both Opens, and l.116 marks ε ≤ 2ε_Φ. l.97's "far below r_B" and l.109's continuity bound now cite ε_{n+1} ≤ 2ε_Φ (*The induction*).
- **C1-1.2, repaired (l.92).**
  - (a) The data's complex part at the evaluation points is s_Z ≤ ((1−β)/2 + h_k/α_{1,k})α_{1,k}L^{−k} ≤ ½α_{1,k}L^{−k}, with h_k ≤ min(β, 1)α_{1,k}/2 (l.47, l.75). So the Schwarz factor is 2, not L/(1+β₀).
  - (b) Each exponential is now bounded by 1, since the distance is 0 for up to N₀ steps and the bounds cumulate (LFR I p.191 l.54–55). The N steps then give a factor N ≤ R_k (LFR II p.361 l.14).
  - (c) The comparison is now explicit. The sum is at most O(1)g_k(log g_k^{−2})^{p₁+(2+β₀)r}L^{−k}, against α_{1,k} = λ_RC₀g_k(log g_k^{−2})^{q₁}, with q₁ = q₀ > p₀ + 3r ≥ p₁ + 1 + 3r (LFR I p.198 l.55). This uses R_m ≤ L(log g_m^{−2})^r (CRE (2.5), table row R_k), log g_m^{−2} ≤ 2log g_k^{−2} for k − m ≤ N₀ (CRE (2.6)), and L^{N₀} = L·R_{k−N₀+1}.
  - Found in the pre-check of C1-2: the Schwarz step scales the complex part by 2 inside Bałaban's post-R spaces. Their conditions (2.34)–(2.37) at the scaled points need the margin of (R-eval-curv). This is marked at l.92 and listed in the Open block (l.6).
- **C1-1.3, repaired (l.91).** (1.45) is printed at the real stages (LFR I p.186 l.5–11). Its use on Bałaban's complex spaces is now the reading *R-chain-cx*: the complex inclusion is stated at p.191 l.39–42 with a proof "almost identical" to (1.44)–(1.52), and VAR p.309 l.2–4 gives the analytic 𝓗. The reading is registered on l.17. The source is now the u-free chain's s_n relative to V^{(j)} (p.188 l.53), with |s_n| ≤ 2c_χδ′_j, so (1.45) reads O(c_χ)B₃δ′_j.
- **C1-1.4, repaired (l.102, l.103, l.106), checked against REG's raw files.**
  - u₁ is the transformation of the inductive hypothesis (p.88 l.18), and Theorem 4's transformation is u = u′u₁ (p.89 l.18), with |u′u₁ − 1| < 16dB₁(α₀ + α₁) "reasoning as in (1.70)–(1.72)" (p.89 l.35).
  - (1.70)–(1.71) bound it at x ∈ B^j(Λ_j) through averages over paths of at most dL^{n+1} bonds. So the note's |λ̂(y)| ≤ 16dL^iη|A_L|_{(0)} stands.
  - w(y) = 1 now rests on VAR's orbit group (4), u(y) = 1 on 𝔅_k (VAR p.278 l.16–19, l.32–33).
- **C1-1.5, repaired (l.116, l.119, l.121).** The sums now run over m ≥ n + 1, since ũ_n is formed after step n's source is used. dev_n then involves only the stages before n, so l.122's induction is explicit. Its count (N + 2) is unchanged.
- **C1-1.6, repaired (l.112, l.117).**
  - f(U) = e^{iF(0, s^{re})}.
  - l.112 now holds the base U of *The data*, and so each U₀, fixed. It says why ũ is G-valued at every real point with that base: 𝕌, 𝕎, 𝕌^{(n)}, and 𝕎_n are real there.
- **Not checked by C1-1, settled in the pre-check:**
  - VAR (190)'s d. VAR p.288 l.45 refers to its [3], which is PRT2 (CMP 96). Its distance (2.46) (PRT2 p.231 l.10–12) counts a contour in blocks of each layer's own scale. So a crossed layer of M-cubes adds at least M, as l.44 says, and l.99's M/M₁ is conservative. Both lines now cite (2.46).
  - The covariance of 𝓗 under real gauge transformations that are not 1 at the block points: by uniqueness of the critical orbit, with the data conjugated at the block points. l.112's statement covers it.
- C1 cannot be clean while (R-eval-curv) stands, through l.92's scaled points and l.113's landing. C1-2 waits for it, like B2.

## (R-eval) Packets B and C1: Pre-Checks Before Launch (3 November)

- **Packet B (i), rewritten on the family.** (i) argued that the points obey 𝒟^{sub}_k's phase condition on the layers newer than k₀, and that the bounds exceed their 𝒟^{sub} values only near Λ. That was false where λ^{(k)}_n > 1, and it left out the 𝐇-part. Now each bound in (i) is stated on 𝒟^λ_k, and Φ(𝐔) ∈ 𝒟^λ_k, so no growth factor is needed. The transports go through A_k, a sup over the evaluation points. Only A_k's size in the response region near Λ is computed.
- **(6C) l.807.** The quarter of exp(−p₀(g_k)) now also lists the transports' factor e^{A_k} ≤ e, the +1 that (i)'s payment bullet uses.
- **Packet B (ii).** Φ(U) = U_k^0(M(U)) on 𝓜, and the pins p.191 l.39–41, p.191 l.33–34, and p.372 l.23–25.
- **Packet C1, l.101 (*The reduced frame*): GAP closed.** The words' equality at the reduced representative was argued as G-invariance continued to G^c. 𝒟_k, like CRE's Ũ^c, is G-invariant only (CRE p.261 l.42–43), and G's gradient is of the order of the complex part, so the gauge path can leave 𝒟_k on the top layer. The equality is now the identity theorem in 𝐔 on 𝓜^c.
  - On 𝓜, ũ is G-valued and the words agree.
  - Both words are analytic: the u-free chain's on the post-R 𝒟_k ((ii)), the reduced chain's while its data stay in VAR's ball r_B and its final stage lands in 𝒟^λ_k.
  - Uniqueness of continuation along P(𝐔_t) from P(U) ∈ 𝓜 gives the equality.
- **Packet C1 pins.** Converted to corrected lines.
  - (190) now cites (189)'s "final result only" (VAR p.308 l.28–30) together with l.36.
  - LFR II p.372 l.14–15, LFR I p.192 l.2–3, and p.191 l.39–41.

## (R-eval) Packets C2, D, and E: Pre-Checks Before Launch (3 November)

C2 is split into C2a (l.112–129: *The induction*, *The sum*, *The scope*, *The M-factored domain*) and C2b (l.130–156: the deformations' gradient and current, *The 𝐉 coordinate*, *The curvature conditions*, *The starting values*). Scopes: `scope_twoloops_RevalC2a1.md` and `scope_twoloops_RevalC2b1.md`.

- **Pins converted to the corrected files.**
  - LFR I p.191 l.25–31 → l.39–45 (the chain statement; l.147 and the header l.10), and p.191 l.20–21 → l.33–34 (the n = 0 space).
  - RG1 p.275 l.1–6 → l.2–4 (l.119 and l.13), and l.3–4 → l.4 (l.142).
  - RG1 p.262 l.59 → l.60 (the start of condition (iv)'s sentence), and RG1 p.270 l.24–27 → l.25–27.
  - LFR II p.369 l.26 → l.25–26, p.366 l.24 → l.23 (U_0^{(AL)}), and CRE p.266 l.7 → l.6.
  - LFR I p.188 l.8–9 → l.4–10 (the decomposition 1 = χ′^{(j)} + (1 − χ′^{(j)}), (1.55), and the exclusion).
- **Pins added.**
  - g_k|B| < δ′_k on Λ: LFR II p.360 l.42, by LFR I (1.82).
  - N ≤ O(1)(log g_k^{−2})^ν: LFR I p.198 l.54, under (1.94).
  - |g_kB′| < M₀ε_k: LFR II p.356 l.37, the display below (1.1).
- **C2a, *The sum*.** The phase along 𝐔_t is t times that at 𝐔 only up to the relative error O(|B|/r_B) of *The scope*; this is now said. The per-bond bound carries C_*.
- **C2a, (deformation + response) ≤ min(β,1)α_{1,k}/4 ≤ h_k.** Checked against map l.942: h_k := min(β,1)α_{1,k}/4 + 8C₁^{RG2}B₀e^{16κ_s}O(1)ε_k ≥ min(β,1)α_{1,k}/4. The arithmetic of l.128 and C_T^{(K)} ≤ 4K·C_T hold for K ≥ 1.
- **C2b, the covariance.** J^h(V^G) = Ad_GJ^h(V) now names Ad_G as Ad_{G(b_−)} at each bond, RG1 (1.10)'s action R(u_−).
- **C2b, *Landing*.** On n ≤ k₀ the bound used λ^{(k)}_n = λ without saying so. It holds since k − n ≥ N₀ and c′^{N₀} ≥ λ for g small (N₀ → ∞, *Where it lands*); now stated.
- **D and E.** Every other pin in l.1–35 and l.157–206 was read against its corrected file and matches.
- **C1, a layout defect.** *The Landau representatives* was run onto the end of *The base*'s line (l.92); it is now its own bullet. The note's lines after l.92 moved down by one, and the prepared scopes follow (C1 l.81–112, C2a l.113–130, C2b l.131–157).
- **C1, REG pins.** REG has no corrected files, so its convention is the raw line minus one. p.80 l.29–31 → l.28–30 (the orbit "depends on an element U chosen to generate" it), p.82 l.20–22 → l.25–26 ("deeper reasons connected with properties of the averaging operations"), p.88 l.29–30 → l.36 (u₁ "determined uniquely in terms of U₁"), and REG (1.70)–(1.71) are on p.88, not p.89. Every other pin of C1 matches. Scope: `scope_twoloops_RevalC11.md`.
- **VAR's δ₀ and B₀.** The note's l.118 cited PBG Theorem 3.1 (p.397 l.37). VAR takes its H-bounds from "Theorem 3.12 from [5]" (VAR p.285 l.25; [5] is PBG, p.309 l.24), whose common rate δ₀ and constant B₀ "depend on d and L only" (PBG p.423 l.39–p.424 l.3). l.118 and l.43 now cite these.

## CRE's C₀ and C₁: the Choice C₀ ≥ C_KC₁ Withdrawn (3 November)

Found while checking the premise C₀ ≥ 8C₁ of a direct derivation for (R-eval-curv).

- **The source.** CRE (2.28) asks only that C₀ and C₁ be "sufficiently large" (p.259 l.50). But CRE p.262 l.43–46 says that some restrictions on α_{0,j} and α_{1,j} "come from the paper [I]. We assume that all of them are satisfied here." RG1 p.277 l.54 assumes B₃²O(1)Mα₀ < ½α₁, so that the deformation exp iξ𝐇_j of (3.37), of size B₃²O(1)Mα₀, lies in the complex part (conditions (i)–(ii) of RG1 p.262). RG1 then gets the curvature and current of the deformed configuration by covariance, from (3.38)–(3.40) with factors exp B₃²O(1)Mα₀ (p.278), not from its size. So C₁ = λ_RC₀ with λ_R = K_RLM + 1, as table row 53 already records, and ᾱ = α₀.
- **What it refutes.**
  - The two-loop note's choice C₀ ≥ C_KC₁ (accepted by the user on 29 October, l.14).
  - l.6's direct reduction of (2.34) at 𝕌̃ to the real base, which needed C₀ ≥ 8C₁.
  - The covariance note's condition M ≥ 2C_avC₁/C₀ (§3(b), (K3); map l.168, l.1614; SW l.103), which fails because λ_R grows with M.
- **Repairs.**
  - The current part of K now uses an α₀-entry in T_Y, C_KB₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k}), with C_K := 128K/(1−β)². The map already carries such an entry with C′ ≥ 16 (l.929, l.1498). So sup|𝐇| ≤ 4min(β,1)α_{0,k}/C_K + O(ε_k), and the current change 2K sup|𝐇| at s ≠ 1 is below ⅛(1−β) of the current room for g small (note l.14, l.137–138, l.154).
  - T₁'s D*D on the layers n ≤ k₀ is now covered by λ ≥ 4C_Λ′M⁵(C₁/C₀)/(1−β) (l.166).
  - In the covariance note, the covariant disc is reduced by μ := min(1, MC₀/(2C_avC₁)) in R_A and in δ̄_m := min(δ̄, μ4^{−m}). Then R ≥ 2 as before, and the per-plaquette term is ≤ α_{0,j}L^{−2j}/(4C_av). Lemma 3's factor becomes 8K₁δ_W/μ + 24L^{−2m}, and Ĉ gets 1/μ in its first series and μ(L/4)^m in its exponent. Ĉ stays finite and independent of k and g. The map's l.168 and l.1614 and SW l.103 were updated.
  - l.6's reduction is replaced by one line saying that it does not work. What is missing is now stated as a margin in (2.34)–(2.37) at 𝕌^{(0)} that absorbs the conjugation by ũ. Bałaban's own device on old layers (CRE p.277 l.2–7) remains the route.
  - The labels "with the choice C₀ ≥ C_KC₁ (accepted by the user)" in the note (l.7, l.8, l.34, l.872), the map (l.193), and the D2.7 closure (l.5, l.7) now name the α₀-entry.
- **Checked unaffected, with C₁/C₀ = λ_R fixed after L and M.** The map's l.1343 and l.1372, l.971's S_H, the D2.6 closure l.73, SW l.93's (1 + 2C₀/C₁) factor, (b2)'s 3λS₃₀λ_Rρ_k, and the non-covariant disc's c_nc and m₀. Each is a constant times an amplitude of order ρ, or needs only α₀/α₁ bounded.
- **(R-eval-curv) reduced to one input (l.6, *The reduction to 𝕌^{(0)}*, derived, not reviewed).**
  - Each quantity in (2.34)–(2.37) at 𝕌̃ is the same quantity at 𝕌^{(0)} conjugated by ũ, or by its block-constant form for the minimisers (RG1 (3.38), p.278 l.3–12, used there at complex u_j).
  - The former third input, a decay bound for λ̂, is derived: both terms of *The bound on G* carry L^iη (l.106, l.108). So |log(ũũ(U)^{−1})| ≤ O((N+1)B_Gλα_{1,k})L^{−(k−n)} on layer n, below ¼β2^{−(k+1−n)} for g small, uniformly in n.
  - The open input is a margin ½β2^{−(k+1−n)} at 𝕌^{(0)}. The T-step's points carry 7/8 of the step margin with C_K ≥ 128. What is not shown is that LFR II (1.65) and the N preliminary steps carry that margin. On Ω_k, LFR I (1.68)'s c = 3 and the response of U_k^0 relative to 𝐔 (T₁, T₂) are the obstacles: the response's complex part has α₁-scale gradient, and C₁ = λ_RC₀.
- **C2a1 was running during these edits.** Its packet contains l.137–138. Its findings on those lines are to be triaged against the current text.

## (R-eval) Packet C2a, Round C2a1: Triage (3 November)

Referee run `referee_cli_20261103-044121_scope_twoloops_RevalC2a1.json` (launched 04:41, finished about 05:05), on note l.122–139. One ERROR and five MINOR findings. All six were accepted and repaired in place on 3 November, between 05:10 and 05:25. The note stays at 948 lines.

- **C2a1-1 (ERROR), l.130: accepted, repaired.**
  - The finding: l.130 extended the whole class's sup bounds to 𝒟^{λ,M}_k. The reduction to 𝓜^c ∩ 𝒟^λ_k was shown only for the old insertions' post-R functions. SW (b2)'s Y_W, the att, lw, and wrap members, and D2.6 5.4's transports are functions of 𝐔 itself.
  - Composing only the old insertions with P fails. At s = 1 with a general step-(k+1) point a″, P_k of the point is not the point, and K enters at the full room.
  - The repair: every member is taken composed with P (l.130, *The bounds*), and at step k+1 the members are Y′∘P_{k+1}. The T-step then needs Y′ only at 𝐕 = P_{k+1}(𝐔) ∈ 𝓜^c_{k+1}, with the old members at P_k of e^{iη𝐇_𝐕(s,tB′)}𝐕. At s = 1 the point is a minimiser, so P_k is the identity there (l.131–136).
  - Values at the real minimisers are unchanged. Values at the real s-decoupled points change, but the cluster expansion uses only s = 1, the s = 0 factorisation, and analyticity in s, and P is localized within the member's domain.
  - The production's estimates cover this a″: SW (b3)–(b4) on the family (l.54), and D2.6 5.4 through *The carry* (l.228). SW (6b)'s R′ is marked Open (R-eval-curv), as l.6 already lists it.
- **C2a1-2 (MINOR), l.8, l.127, l.129, l.156: accepted, repaired.**
  - "As Bałaban's extension does" and "the form of Bałaban's T-step" are removed. l.127 now quotes LFR II p.374 l.38 ("in the usual way into the localized function 𝐇_k … hence into u_{k,Λ}") and p.375 l.11–12. It states that the M-factored function is the note's own, and that the two agree on the graph {(𝐕, J^h(𝐕)) : 𝐕 ∈ 𝓜^c}. The proof: they agree at (U, J(U)) for U ∈ 𝓜, which is totally real of maximal dimension in the graph.
  - l.129 now quotes RG1 p.275 l.2–5 in full: the background is U_{k+1}(□₀, M·(𝐔)), "extended as equal to 𝐔 outside □₀". D27 l.7 is updated to match.
  - 𝒟^{λ,M}_k's definition (l.129) now requires both (V̂, 𝐉) and (V̂, J^h(V̂)) in 𝒟^λ_k. The old terms take J^h(V̂). l.163 already used this current condition "by the definition", so the definition had to state it.
  - l.156 now applies (1.65) at (V̂, J^h(V̂)), which lies in 𝒟^λ_k ⊂ 𝒟_k ⊂ Ũ_k^c by the definition, through the identity on the graph.
  - At the T-step's points, J^h of the point lands by l.54's transfer: J^h(𝐕) in step k+1's condition, 𝐇_𝐕's current within the ¼(1−β), and the quadratic terms O(λ_Rh_k) of the room (l.136).
- **C2a1-3 (MINOR), l.126, l.130: accepted, repaired.**
  - The representative argument is written out in l.130 (*The bounds*, "The representatives"). a″'s part needs no gauge change, since R_k = R_kR_{k+1} at the common base (REG p.80 l.10–16; N(Q′_k) ⊂ N(Q′_{k+1})). 𝐇's part goes into the step-k gauge as at SW (b3)'s points.
  - 𝐇_𝐕 at the complex background obeys SW (b3)'s bounds. This is R-dec read at the complex background, accepted from RG1 p.275 l.6–7 ("all necessary theorems are valid for operations with this configuration") and VAR Proposition 9's G^c-valued V′.
  - The BCH term is O(h_kα_{1,k})L^{−k}, below ⅛(1−β)α_{1,k}L^{−k}.
  - A Cauchy estimate of 𝐇_𝐕 − 𝐇 in the background was considered and not used. The background's analyticity radius is of the order of a″'s room, so it would give only a first-order relative bound.
  - l.126's "a″ real and nonzero" is removed. The real non-minimisers are now real 𝐕 and B′ with s ∈ (0, 1).
- **C2a1-4 (MINOR), l.130: accepted, repaired.** l.130 marks Open (R-eval-old) and Open (R-eval-curv) where the class's bounds are used.
- **C2a1-5 (MINOR), l.138: accepted, repaired.** The α₀-entry's constant is C_K′ := max(C′, C_K), so T_Y is at most the map's l.1498 whatever enlargement l.1614 makes of C′.
- **C2a1-6 (MINOR), l.138, l.139: accepted, repaired.**
  - (a) l.139 now lists c_M (map l.1517), and through it C_M and C_S′, besides θ_k's (β) term. All are fixed after L, M, and β.
  - (b) The repair found a gap. The s ≠ 1 response 2K sup|𝐇| does not decay with the layer, and it was compared with h_k only. With β near 1, 2K·min(β,1)α_{1,k}/(16K) does not fit SW (b3)'s uniform margin ½(1−β)α_{1,k}, and the table's range is β ∈ [3/4, 1).
  - The repair: T_Y's second entry carries 1/(1−β), with h_k^{(K)} ≤ (1−β)min(β,1)α_{1,k}/(16K) + O(ε_k). On an older layer the response is ≤ ¼(1−β)α_{1,k} and the 𝐇-part ≤ (1−β)α_{1,k}/16, which is ⅜(1−β) in total. With the representatives' ⅛(1−β) this is inside the margin.
  - C_T^{(K)} ≤ 8K(1−β)^{−2}C_T. "4K" is now "4K/(1−β)" at l.8, l.14, and D27 l.7. The sub-bullet's title *T_Y reduced by 4K* is kept, since it is referenced at l.6, l.14, l.76, l.222, and l.228.
  - D2.6 4.2's layer-decaying comparison now covers the 𝐇-part only.
- **Also fixed:** D27 l.7's pin LFR I p.191 l.25–31 is now l.39–45 (p191_corrected.tex l.41–42 is the chain statement).
- **Next:** C2a2 on l.122–139 after C2b1, since C2b1's packet (l.140–166) contains l.156 and l.163, which these repairs touch.
- **Propagated while C2b1 ran (launched 05:22; outside its packet).**
  - l.14: the α₀-entry's constant is C_K′ = max(C′, C_K).
  - l.15: "Bałaban's own form of the T-step" is now "agrees with Bałaban's T-step inside □₀ (RG1 p.275 l.2–5) and is the note's own extension outside it".
  - l.214, l.218 (packet E1): the reason Bałaban's U_k^0 does not do is restated for evaluation without P_{k+1}. With P, a re-minimisation enters only at s ≠ 1, of the order of sup|𝐇|, and T_Y absorbs it.
  - The D1 scope's test (i) now names C_K′ and T_Y's factor 4K/(1−β).

## (R-eval) Packet C2b, Round C2b1: Triage (3 November)

Referee run `referee_cli_20261103-052208_scope_twoloops_RevalC2b1.json` (05:22–05:40), on note l.140–166. Four ERRORs and three MINORs. All seven were accepted and repaired by 05:45; C2b1-2 is repaired by marking, as part of Open (R-eval-curv). The note stays at 948 lines.

- **C2b1-1 (ERROR), l.72, l.166, l.14: accepted, repaired.**
  - λ := 8max(C_Λ, C_Λ′λ_R)M⁵/(1−β) at l.72, since T₁'s D*D is measured against α_{0,k} = α_{1,k}/λ_R and λ_R = K_RLM + 1 grows with M.
  - l.166's layers k₀ < n ≤ k now state the current bound C_Λ′λ_RM⁵e^{−δ₀M/(16M₁)}, which is ≤ ¼(1−β) for M large since λ_R is linear in M.
  - l.14 no longer lists T₁'s current among the source terms that g_K small absorbs.
  - Table row 128 is updated (b7519b43d39f, announced to the peer).
- **C2b1-2 (ERROR), l.156, l.158, l.6: accepted, marked Open (part of (R-eval-curv)).**
  - The graph identity holds at (P(𝐔), J^h(P(𝐔))), not at V̂. P(𝐔) is VAR's axial minimiser, and V̂ is its Landau form, a G^c transform that is ≠ 1 at the block points (l.106).
  - Ũ_k^c is G-invariant only (LFR I p.191 l.32–33; CRE p.261 l.42–43). So (P(𝐔), J^h(P(𝐔))) ∈ Ũ_k^c(Y₄) needs the margin of (R-eval-curv).
  - l.156 states this, l.158 is now conditional on it, and l.6's list of places needing the margin adds this point.
- **C2b1-3 (ERROR), l.152: accepted, repaired.** The old terms' J_n(M·(𝐔)) are CRE (2.37)'s 𝐉_{p,X}(M·𝐔). They are quoted at the u-free representative and are Open (R-eval-curv) at the reduced one, now marked. *The current of the deformations* bounds the evaluation configuration's own J^h, which is (2.36)'s.
- **C2b1-4 (ERROR), l.160: accepted, repaired.**
  - The post-R configuration is the global U_{𝐁_k}(V) ((1.35)), and U_{k,Z} is Z-local (LFR I p.192 l.52–55).
  - δ^{re} now has a second part, the replacement of U_{k,Z} by U_k. Bałaban makes it "in the same way as above … with some new small terms" (LFR II p.365 l.34–35), and the representation above it has its 𝐇-argument supported at ∂Z^{∼−3} and bounded by 44d²ε_k (p.365 l.28–29).
  - That passage is read as the same representation with the same bound, Bałaban's "small terms", accepted. The part is O(B₀d²ε_k).
  - |δ^{re}| ≤ O(B₃M₀ + B₀d²)ε_k, propagated to l.45, l.161, and l.165.
- **C2b1-5 (MINOR), l.148: accepted, repaired.** The bound is now pointwise, |ΔJ| ≤ O(c_χS_L)δ′_j(L^iη)^{−3}, with |λ̂| ≤ B_GL^iηε_{n+1} (l.120). The (−2)-norm conclusion is unchanged.
- **C2b1-6 (MINOR), l.147: accepted, repaired.** The coefficient is O(|a|). D* of the nonlinear part is bounded through its first differences, (L^iη)²|a||∇a| ≤ εγ, which is uniform in k.
- **C2b1-7 (MINOR), l.164: accepted, repaired.** T₁'s source is now l.43's O(1)L^j(C_{rsp}M⁵ + 1)s_Z per j-block, by (1.41) and (190), with C_{rsp} ∝ γ₀^{−1}B₃². The citation of (1.45) is gone.
- **Noted while checking:** CRE p.261 l.42 takes β = 1/4, and LFR I p.191 l.35 needs β ≤ 1/4 for the spaces to descend. The 1/(1−β) added to T_Y in round C2a1 is therefore only conservative.
- **Found after the round: the C2a1-1 repair broke locality (05:45–06:05), repaired.**
  - Composing every member with the global P changes the members that are functions of 𝐔 (SW (b2)'s Y_W, the att, lw, and wrap members, and D2.6 5.4's transports) into functions of M(𝐔) everywhere, through (190)'s decay. The T-step's factorisation at s = 0 needs local members.
  - Bałaban's T-step evaluates the old terms at local minimisers, U_j(□₀, ·) with X ⊂ □̃² and □₀ = □̃⁵ (RG1 p.273 l.37–45, (3.23) p.274).
  - Repair at l.130: those members are composed with P_Ω(𝐔) := U_{𝐁_k,Ω}(M·(𝐔)), the minimiser for CRE's localized determining set (2.13)–(2.15) (p.256 l.55–p.257 l.20).
  - Locality: Γ₀ = Ω₁^c carries M⁰ (CRE (2.2), (2.11)), so every bond off Ω₁(Ω) is pinned, and dist(Ω₁(Ω), Ω^c) ≥ ξM₁ (p.256 l.61).
  - Identity on 𝓜: every admissible W equals U off Ω₁(Ω) and has U's 𝐁_k-averages, so U minimises, and VAR Theorem 1's uniqueness applies. Bałaban prints the instances RG1 p.273 l.45 and LFR II (1.61). The identity principle extends it to 𝓜^c.
  - At s ≠ 1, VAR Proposition 9 holds for the localized set, whose minimisers are CRE's U_{p,X} (p.261 l.10). The factor 4K/(1−β) in T_Y is unchanged.
  - l.7, l.8, l.129, l.213 and D27 l.7 are propagated. No Open remains from it.
- **Next:** C2a2 (l.122–139), then C2b2 (l.140–166).

## (R-eval) Packet C2a, Round C2a2: Triage (3 November)

Referee run `referee_cli_20261103-060116_scope_twoloops_RevalC2a2.json` (06:01–06:27), on note l.122–139. Two ERRORs and six MINORs; all eight were accepted and repaired between 06:28 and 06:36. The referee confirmed C2a1-1 to C2a1-6 as repaired. The note stays at 948 lines.

- **The premise of the locality bullet above was wrong.** P is not global: U^{post} := U(𝐁_k″(Y₁), ·) (l.39) is CRE's localized form (2.14), supported in Y₁. Both ERRORs came from the separate P_Ω built on 𝐁_k.
- **C2a2-1 (ERROR), l.130: accepted, repaired.**
  - The transfer used P_{k+1} as if global, and P_{k+1}∘P_Ω = P_{k+1}.
  - Now each member takes the P of its own localization domain, at every step. P_{k+1} is the step-(k+1) member's own localized projection, so the background 𝐕 = P_{k+1}(𝐔) is local, as Bałaban's U_{k+1}(□₀, M·(𝐔)) is (RG1 p.275 l.4–5).
  - The step-(k+1) member's domain Y′ contains each constituent's own domain (its Ω or Y₁) in Y′⁰, so the constituent's P_k is the identity at the s = 1 points.
- **C2a2-2 (ERROR), l.130, l.8: accepted, repaired.**
  - P_Ω is now U(𝐁_k″(Ω), ·) with 𝐁_k″(Ω) := 𝐁(Ω) ∪ 𝐁_k″, which is U^{post} with Ω in place of Y₁.
  - The identity is stated as a lemma: a localized minimiser map U(S, ·) is the identity on the minimisers of every S′ that equals S or is coarser on S's support.
  - It covers the 𝐁_k-minimisers, the 𝐁_k″-minimisers, and 𝓜(Y₁′) for Ω ⊂ Y₁′⁰ (LFR II p.373 l.26–27).
- **C2a2-3 (MINOR), l.127: accepted, repaired.** The agreement holds as far as the graph lies in Ũ_k^c(Y₄) (LFR II p.375 l.17–20). At (P(𝐔), J^h(P(𝐔))) this is marked Open (R-eval-curv).
- **C2a2-4 (MINOR), l.99, l.130: accepted, repaired.**
  - (a) l.99 now covers the strip Y∖Y⁰. Its layers have dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁ (CRE p.256 l.61), so a crossed strip layer adds at least M₁ to d.
  - The condition δ₀M₁/16 ≥ (d+1)log L + 1 follows from table rows 34 and 44: M₁ = KM′, K ≥ 12d + 1, and δ₀M′ ≥ 64 log L give δ₀M₁/16 ≥ 4(12d+1)log L.
  - (b) The dangling *At s ≠ 1* is gone. K for 𝐁_k″(Ω) is derived as for 𝐁_k″(Y₁) through l.99.
- **C2a2-5 (MINOR), l.136: accepted, repaired.** 𝐇_𝐕's current part is now l.14's ⅛(1−β)f_nα_{0,k}, so the budget is ¾ + ⅛ + ⅛ = 1.
- **C2a2-6 (MINOR), l.130, l.17: accepted, repaired.** R-dec at the complex background is now the named reading *R-dec-cx*, listed at l.17 with R-chain-start and R-chain-cx.
- **C2a2-7 (MINOR), l.130: accepted, repaired.** The several-layer case is CRE p.257 l.22–26.
- **C2a2-8 (MINOR), l.129: accepted, repaired.** 𝒟^{λ,M}_k is defined with each member's own localized projection.
- **C2b1-2 (restated by the referee):** the sup reduction now reads "|Y| at the points P(𝐔) of 𝓜^c whose representative V̂ has (V̂, 𝐉) ∈ 𝒟^λ_k", which is what (iii) bounds. The G^c transfer at V̂ for (1.65) stays part of Open (R-eval-curv).
- **Propagated:** l.8, l.213, l.218, and D27 l.7.
- **Next:** C2b2 (l.140–166), then C2a3 (C2a needs two clean rounds).

## (R-eval) Packet C2b, Round C2b2: Triage (3 November)

Referee run `referee_cli_20261103-063520_scope_twoloops_RevalC2b2.json` (06:36–06:54), on note l.140–166. No ERROR and six MINORs. The referee confirmed C2b1-1 to C2b1-7 as repaired. All six were accepted and repaired by 07:05; the note stays at 948 lines. C2b1-3, C2b2-1, and C2b2-3 were real gaps, so C2b needs another round.

- **C2b2-1 (MINOR, real gap), l.166: accepted, repaired.**
  - T₁ now takes ⅛(1−β) on both ranges of layers; l.72's λ = 8max(C_Λ, C_Λ′λ_R)M⁵/(1−β) already meets this.
  - An explicit current budget now runs: data (4/7)(1−β) (l.54, β₀ = 1/7), 𝐇_𝐕 (1−β)²/16 (l.14), quadratic terms (1−β)/32, T₁ ⅛, T₂ and the base change (1−β)/32, and the deformations ⅛. The total is 0.947(1−β) < f_n.
- **C2b2-2 (MINOR), l.162, l.164: accepted, repaired.** Δd⁰ = 0 on Λ^{old}, so T₁'s source covers all of Λ. On Λ^{old} the source is −Δd, bounded by l.43's "+1", which covers "the difference on the rest of Λ, where U_k^0 takes the real V″".
- **C2b2-3 (MINOR, real gap), l.129, l.151, l.153, l.159, l.163, l.11: accepted, repaired.**
  - 𝒟^{λ,M}_k now requires (V̂, R(u_L)𝐉) ∈ 𝒟^λ_k, the Landau form of the pair (P(𝐔), 𝐉) (RG1 (1.10)).
  - l.151, l.159, and l.163 say "at the representative V̂". Only V̂'s complex part enters.
  - For CRE's B-terms (G-covariant only), the bounds at (P(𝐔), 𝐉) from the membership of the G^c transform go through Open (R-eval-curv), now marked at l.153.
- **C2b2-4 (MINOR), l.160: accepted, repaired.** The pins are now LFR II p.365 l.35–36 and l.29–30.
- **C2b2-5 (MINOR), l.160, l.17: accepted, repaired.** The replacement of U_{k,Z} by U_k is now the named reading *R-small-Z*, listed at l.17, and the note says that Bałaban prints neither the representation nor the bound for it.
- **C2b2-6 (MINOR), l.159, l.161: accepted, repaired.**
  - The starting values are stated where the real base is a post-R background on the support of the R-step's indicators, which covers the T-step's points with l.137's base. At a general real point of 𝓜, |δ^{re}| = O(ε_k) is not claimed.
  - l.161 now uses only (L^iη)|R₀| ≤ O(S_L)|δ^{re}|, which the base change needs.
- **Next:** C2a3 (l.122–139, with l.99's strip and R-dec-cx), then C2b3.

## (R-eval) Packet C2a, Round C2a3: Triage (3 November)

Referee run `referee_cli_20261103-065645_scope_twoloops_RevalC2a3.json` (07:06–07:15), on note l.122–139 with l.99 and l.17. Two ERRORs and three MINORs. The referee confirmed C2a2-2 to C2a2-8 as repaired, and C2a2-1's locality half. The lemma on minimisers, the locality of P and P_Ω, l.99's strip, and R-dec-cx's sources check out. The note stays at 948 lines.

- **C2a3-1 (ERROR), l.130, l.131, l.136: accepted, marked Open (R-eval-transfer)(a).**
  - With P_{k+1} localized, the real points of 𝓜_{k+1}(Y′) are localized minimisers pinned off Ω₁(Y′). RG2's identity (map l.108 (ii)) holds at the global minimisers only, which are not a uniqueness set there. At a real localized 𝐕 with B′ = 0 the claim would make 𝐕 a global minimiser.
  - Bałaban never claims the identity. He re-projects with U_j(□₀, M·(·)) after deforming (RG1 (3.24)–(3.25)).
  - Route stated at l.130: compare with the global background on Y′⁰, using (190)'s decay from ∂Y′, with a collar wide enough that K times the decay fits (1−β)/32. Not carried out. l.131 and l.136 are restricted to global backgrounds.
- **C2a3-2 (ERROR), l.130, l.136: accepted, marked Open (R-eval-transfer)(b).**
  - R_k = R_kR_{k+1} gives only the step-k Landau condition. V̂ is also fixed by REG's normalisation at the layer-k points (REG p.80; l.102–103), while e^{iηa″}U_{k+1} is normalised at the step-(k+1) points only.
  - The two differ by a complex gauge function ν ∈ N(Q′_{k+1}) ⊖ N(Q′_k), first order in a″ with an O(1) constant. 𝒟^λ_k is G-invariant only.
  - Route stated: bound ν through REG (1.70)–(1.71), as *The bound on G* does, and carry it as G is carried in *The reduced frame*. Not carried out.
- **C2a3-3 (MINOR), l.137: accepted, repaired.** The s ≠ 1 current budget is now explicit: (4/7 + 1/16 + 1/32 + 1/16)(1−β) + o(1) < ¾(1−β), with the response at l.14's (1−β)²α_{0,k}/16 + O(Kε_k).
- **C2a3-4 (MINOR), l.99: accepted, repaired.** CRE's integer is now K_{CRE}, distinguished from VAR's factor K.
- **C2a3-5 (MINOR), l.130: accepted, repaired.** The iteration of the averages is cited as CRE (2.11) (M_S = M^j on Γ_j, with M^j the j-fold average), not RG1 (3.3).
- **Propagated:** the new Open is named at l.7, l.8, l.38, l.213, and D27 l.7.
- **Next:** C2b3, which does not depend on the transfer; then E1. C2a waits for (R-eval-transfer).

## (R-eval) Packet C2b, Round C2b3: Triage (3 November)

Referee run `referee_cli_20261103-071800_scope_twoloops_RevalC2b3.json` (07:18–07:37), on note l.140–166 with l.17's R-small-Z. One ERROR and four MINORs. The referee confirmed C2b2-1 to -4 and -6 as repaired, and C2b2-5 as named (R-small-Z). The recursions, the covariance identity, the rotation and mixed-difference terms, the 𝐉 coordinate pins, the decomposition, the Cauchy factor, and λ's two conditions check out. The note stays at 948 lines.

- **C2b3-1 (ERROR), l.156 with l.6 and l.127: accepted, Open (R-eval-curv) widened.**
  - Membership of (P(𝐔), J^h(P(𝐔))) in Ũ_k^c(Y₄) also needs CRE (2.39) at the axial form P(𝐔) (CRE p.261 l.35–40). 𝒟^{λ,M}_k bounds phase and gradient only at V̂.
  - The non-unitary part of u_L shifts A′ by D(Im λ̂) at first order. l.107 bounds D₀λ̂ only through the configurations' own fields, so the bound is circular. On Ω_k the two rooms coincide (l.52–53).
  - Not derivable from the print with room. Added to Open (R-eval-curv): in the heading at l.6, a paragraph at l.6's end with the route: apply (1.65) at (V̂, J^h(V̂)), which is in 𝒟^λ_k ⊂ Ũ_k^c(Y₄) by definition, and carry the image back by RG1 (3.38)'s block-constant complex-gauge covariance (p.278 l.3–12). That reduces the part to l.6's margin, but needs the covariance for LFR II's whole U_k^0 ((1.50)–(1.51)). It is not carried out. and at l.127, l.156, and l.158. The E1 and D1 scopes declare it.
- **C2b3-2 (MINOR), l.166 with l.137: accepted, repaired.**
  - l.14 now keeps T_Y's min(β,1) with β ≤ 1/4 (CRE p.261 l.42 takes β = 1/4; LFR I p.191 l.35 needs β ≤ 1/4, both checked). 𝐇_𝐕's current and l.137's response are each at most (1−β)²/64 + O(Kε_k).
  - l.137: (4/7 + 1/64 + 1/32 + 1/64)(1−β) + o(1) < ¾(1−β).
  - l.166 now includes the s ≠ 1 response: (4/7 + 1/64 + 1/32 + 1/64 + 1/8 + 1/32 + 1/8)(1−β) + o(1) ≈ 0.915(1−β) < 0.92(1−β).
  - The gradient at s ≠ 1 is cited to l.138 (inside SW (b3)'s margin).
- **C2b3-3 (MINOR), l.160: accepted, repaired.** The RG2 (1.18) quote is replaced by VAR Proposition 9 / (190) with the factor K, so the R-small-Z part is O(Kd²ε_k). B₀d² became Kd² at l.45, l.160, l.161, and l.165, and C_mx := O(1)L(B₃M₀ + Kd²)/r_B at l.45. Table row 128 now carries the same C_mx and δ^{re}'s bound. The first edit was reverted at once for the peer's r34 hold, and re-applied after r34 landed: 15bad0c974a2 → 5b705fee9701.
- **C2b3-4 (MINOR), l.154, l.159, l.166: accepted, repaired.** l.159 and l.166 mark part (a) of Open (R-eval-transfer). l.154 marks part (b), and at s ≠ 1 also Open (R-eval-curv) for (2.36) at P of the point.
- **C2b3-5 (MINOR), l.157–158 and l.6: accepted, repaired.** The reading *R-coincides* (at n = 0 CRE's radii, per p.191 l.33–34's "coincides", over (1.68)'s c = 3 on Ω_k) is named at l.17 and l.157–158 and cited at l.6. The l.6 pin is corrected to p.191 l.13–14 (checked).
- **Next:** E1. C2b4 runs after E1, since C2b3 had an ERROR. C2a waits for (R-eval-transfer).

## (R-eval) Packet E1, Round E1a: Triage (3 November)

Referee run `referee_cli_20261103-074417_scope_twoloops_RevalE1.json` (07:44–07:55), on note l.167–172 and l.213–218. One ERROR and five MINORs. The referee confirmed A_k's definition, the unitarity argument, the bound c_πλα_{1,k}ℓ_k(S), the M⁵ with M = L^m, the cited multi-scale constants' dependence on d and L, and the closing bullet's citations. The note stays at 948 lines.

- **E1-1 (ERROR), l.167: accepted, repaired.**
  - (iv) took r^{an}_k/α_{1,k} → 0 from LFR I's p₁ < p₀. READINGS R43 withdrew that import into CRE (3.43), whose p₁(·) is undefined. Under the slip reading p₁ → q₁ (TRANSCRIPTION_FINDINGS, LFR II p.368), r^{an}_k = α_{1,k} and the landing fails.
  - Repair: r^{ext}_k := min(r^{an}_k, c_{ext}α_{0,k}) with c_{ext} := (1+β₀)/(LK). This holds under either reading.
  - Propagated to D2.7 15.6(d) (definition, |D_g| bound, and b_W), 15.7 (the cluster masses and C^R_k; the order of 1/(r^{ext}_kρ̃_k) is g_k^{−2}·polylog under either reading, with 1/c_{ext} fixed after L and M), the map's l.342, and the note's l.25 and l.36.
  - The wrong pin (q₁ ≥ p₀ "map l.108") went with the removed sentence.
- **E1-2 (MINOR), l.167: accepted, repaired.** (iv) now derives all three conditions at U^{post}(V_k) ∈ 𝓜^c, via VAR Proposition 9 and (190) with K. The current is measured against its room α_{0,k}, hence α_{0,k} in r^{ext}_k. The pair's 𝐉 is J^h of the point. (iv) also marks Open (R-eval-old) and Open (R-eval-curv), the latter including (2.39) at P.
- **E1-3 (MINOR), l.172: accepted, repaired.** Open (R-eval-old) is marked, and (iv)'s extension-domain points are added to the list.
- **E1-4 (MINOR), l.8, l.38, l.154, l.172, l.213, l.218 and D27 l.7: accepted, repaired.** Open (R-eval-transfer) now reads "(a) at a localized background, (b) REG's step-k normalisation at any background". l.213 is stated "with the readings of l.17". READINGS.md entries are not required for YM4 (the Bałaban READINGS gates are obsolete for this work).
- **E1-5 (MINOR), l.215: accepted, repaired.** The sentence now reads "only single-scale constants", and PRT II p.246 l.28–29's single-scale H_j′ rate is added (checked).
- **E1-6 (MINOR), l.217: accepted, repaired.** LFR I (1.66) (p.190 l.40–48) gives L₀^{2(k−m)}α_{1,k}L^{−k} on k₀ < m ≤ k. With L₀² ≤ L/3 the Schwarz bound fits layer k − 1 (< ½), but not layer k − 2 or the layers n ≤ k₀ (p.190 l.24–29), all checked. The point of the bullet stands.
- **Next:** C2b4, then E1b.

## (R-eval) Packet C2b, Round C2b4: Triage (3 November)

Referee run `referee_cli_20261103-080050_scope_twoloops_RevalC2b4.json` (08:01–08:19), on note l.140–166 with l.14, l.137, and l.17's R-small-Z and R-coincides. No ERROR and two MINORs. All of C2b3-1 to C2b3-5 are confirmed repaired. Also confirmed: the gradient and current recursions, the 𝐉 coordinate, the curvature pins, both readings, the starting values, and the arithmetic (0.9152(1−β) at l.166, 0.634(1−β) at l.137, and l.14's (1−β)²/64). Not clean, so C2b5 follows.

- **C2b4-1 (MINOR: an unmarked open), l.159 and l.166: accepted, repaired.** At s ≠ 1, V̂'s membership needs (2.34)–(2.37) at P of the point. l.159 and l.166 now mark Open (R-eval-curv) there.
- **C2b4-2 (MINOR: pins and a quote), l.152, l.157: accepted, repaired.**
  - LFR I p.191 l.39–45 → l.39–44: the statement ends at l.44 (checked). Corrected at l.6, l.12, l.157, and in D27 l.7.
  - RG1 p.262 l.60 → l.61, where the substitution sentence starts (checked). Corrected at l.127 and l.152.
  - The "almost identical" quote is now verbatim.
- **Unstated condition: added.** At s ≠ 1 the gradient budget on the older layers uses λ^{(k)}_n ≥ c′ ≥ 2. Table row 12's L ≥ 12d + 6 gives c′ ≥ 5.9 with β ≤ 1/4 and β₀ = 1/7. This is stated at l.166.
- **Next:** E1b, then C2b5.

## (R-eval) Packet E1, Round E1b: Triage (3 November)

Referee run `referee_cli_20261103-082016_scope_twoloops_RevalE1b.json` (08:21–08:34). No ERROR and four MINORs. E1-1 to E1-6 are confirmed repaired. Also confirmed: (190)'s layer weights at U^{post}(V_k), the two p₁ readings and their pins, A_k and l.172's marks, l.213, l.215–218, and the propagation into D2.7 15.6(d), 15.7, and map l.342 (C^R_k survives; 1/c_{ext} is fixed after L and M). E1b-1 is a real gap, so E1c follows.

- **E1b-1 (MINOR, real gap), l.167: accepted, repaired.**
  - Under the slip reading r^{ext}_k = c_{ext}α_{0,k} ≫ M₀ε_k. So a real base taken as "the real minimiser of the real data" on the Cauchy disc can leave the R-step support, where l.159 and *The real base points* derive nothing.
  - Repair, the referee's first fix: the real base is the support point V_k⁰ itself. The disc's points, of deviation tε₀/|ε₀| with |t| < r^{ext}_k, are within 2r^{ext}_k of V_k⁰. Their whole deviation, real and imaginary together, counts as the g^c-valued complex part (CRE (2.39)) and is at most 2Kr^{ext}_k ≤ ((1+β₀)/L)α_{0,k}, with c_{ext} := (1+β₀)/(2LK). When |ε₀| ≥ r^{ext}_k, (c)'s bound at V_k⁰ suffices.
  - The support restricts the integration variable B′ (|B′| < M₀g_k^{−1}ε_k, LFR II p.356, read).
- **E1b-2 (MINOR), l.167: accepted, repaired.** "The same domain under both" is replaced by: under both readings r^{ext}_k ≤ c_{ext}α_{0,k} and r^{ext}_k is g_k·polylog, which is all that is used. r^{an}_k := g_kC₁p₁(g_k) now carries the g_kA scaling mark of D2.7 15.7.
- **E1b-3 (MINOR), consumers: accepted, repaired.** D2.7 l.3, l.5, and l.7, map l.342, and the continuum note's l.3 and l.5 now name (R-eval)'s three opens and say "in review".
- **E1b-4 (MINOR), D2.7 15.6(c) and (f): accepted, repaired.** B(g) is now stated on (d)'s domain of radius r^{ext}_k, and (f) works on that domain.
- **Next:** C2b5, then E1c.

## (R-eval) Packet C2b, Round C2b5: Triage (3 November)

Referee run `referee_cli_20261103-083752_scope_twoloops_RevalC2b5.json` (08:38–08:57). No ERROR, and one MINOR that is a wrong section pointer, not a gap. This counts as C2b's **first clean round**. C2b4-1, C2b4-2, and the c′ condition are confirmed (c′ ≥ 21L/64 ≥ 5.9; the older-layer gradient needs λ^{(k)}_n ≥ 16/11, the phase ≥ 2). The recursions, the budgets (0.915 and 0.634), the 𝐉 coordinate, the curvature quotes, the starting values (T₁'s decay agrees with LFR I p.200 l.13–19), both readings, every open mark, and every pin check.

- **C2b5-1 (MINOR: pointer), l.166: accepted, repaired.** The pointer is now "*The R-step lands in the family*, l.72–75".
- **Observation taken up, l.152.** The old terms' space U^c_j is RG I's union of G^c-orbits (RG1 p.262 l.13; CRE p.259 l.40–45, checked; table §11 row 219), and the old terms are G^c-invariant (RG1 (1.19)). So the old terms at the reduced representative need no transfer. Only (2.37) at 𝕌̃, as a condition of the class's 𝒟_k, stays in Open (R-eval-curv). This narrows the open's description; the open itself is unchanged.
- **Next:** E1c, then C2b6 (the second clean round needed; the l.152 change is in its packet).

## (R-eval) Packet E1, Round E1c: Triage (3 November)

Referee run `referee_cli_20261103-085839_scope_twoloops_RevalE1c.json` (08:59–09:13). No ERROR and four MINORs. E1b-1 to E1b-4 are confirmed repaired. Also confirmed: both p₁ readings, the 2r^{ext}_k geometry, the K bound, A_k, l.213–218, every Cauchy factor, C^R_k, and the consumers' status lines. E1c-1 is a real gap, so E1d follows.

- **E1c-1 (MINOR, real gap), l.167 and D2.7 l.187: accepted, repaired.** The domain is now the 2r^{ext}_k-neighbourhood of the real support, which (iv)'s argument covers with V_k⁰ as base. D2.7 (c), (d), and (f) are stated on it. (d) includes the case ‖ε₀‖ ≥ r^{ext}_k, where V_k⁰ itself is in the domain.
- **E1c-2 (MINOR), l.167 and l.6: accepted, repaired.** (iv) marks (2.34)–(2.37) at V̂ as Open (R-eval-curv), and l.6 lists the extension-domain points.
- **E1c-3 (MINOR), l.172: accepted, repaired.** The switch to 𝕌̃ (l.111/113's identity theorem) and the B-term slots at U^R (l.153) are marked Open (R-eval-curv). The phase bound itself uses no curvature condition.
- **E1c-4 (MINOR), D2.7 l.5: accepted, repaired.** "(R-eval-cr), derived and not reviewed", as the note's l.220 states.
- **Next:** C2b6, then E1d.

## (R-eval) Packet C2b, Round C2b6: Triage (3 November)

Referee run `referee_cli_20261103-091417_scope_twoloops_RevalC2b6.json` (09:16–09:31). No ERROR and two MINORs. C2b5-1 is confirmed repaired. The recursions, the covariance, the expansion, the base changes, T₁, T₂, both budgets, the gradient (λ^{(k)}_n ≥ 17/12, phase ≥ 2, c′ ≥ 5.9), every pin, and all open marks but one check. The no-transfer step for the old terms is confirmed valid. C2b6-1 misstated an open's extent, so this round is not counted as clean, and C2b7 follows.

- **C2b6-1 (MINOR: extent of an open), l.152: accepted, repaired.** The u-free quote is now stated "given (1.65)'s application at (P(𝐔), J^h(P(𝐔))) (Open (R-eval-curv), l.156 and l.158)". "Only (2.37) at 𝕌̃" is restricted to the passage from the u-free to the reduced representative.
- **C2b1-7's last clause (MINOR, no effect), l.165: accepted, repaired.** T₂'s D*D is O(λ_RK²(B₃M₀ + Kd²)ε_k/r_B) times the current room. It still vanishes with g, since λ_R is fixed before g.
- **Next:** E1d, then C2b7.

## (R-eval) Packet E1, Round E1d: Triage (3 November)

Referee run `referee_cli_20261103-093224_scope_twoloops_RevalE1d.json` (09:33–09:42). No ERROR and one MINOR. E1c-1 to E1c-4 are confirmed repaired. Also confirmed: both Cauchy cases, the p₁ readings (CRE p.276 l.30–31 is the only occurrence), the 2Kr^{ext}_k bound, A_k and its marks, the l.213–218 pins, every r^{ext}_k factor, and C^R_k. E1d-1 is a real misstatement, so E1e follows.

- **E1d-1 (MINOR), l.167: accepted, repaired.**
  - U^{post} takes 𝐁_k″(Y₁)-data, which are finer on Z than the post-R data V_k.
  - The configuration is now U_k(V_k) = U_{𝐁_k}(V_k). It is in 𝓜^c up to a gauge transformation by l.133–135 (checked: nesting, and LFR II (1.61)'s localization).
  - VAR Proposition 9 and (190) are applied to the 𝐁_k-minimiser directly, with K the larger of VAR's factors for 𝐁_k, 𝐁_k″(Y₁), and 𝐁_k″(Ω), and c_{ext} uses that K.
- **Next:** C2b7, then E1e.

## (R-eval) Packet C2b, Round C2b7: Triage (3 November)

Referee run `referee_cli_20261103-094320_scope_twoloops_RevalC2b7.json` (09:43–09:57). No ERROR and one MINOR. C2b6-1 (main part) and C2b1-7's λ_R clause are confirmed repaired. Also confirmed: the recursions, the covariance, the expansion, δ^{re}, T₁ and T₂, both current budgets (0.915 < 0.92 and 0.634 < ¾), the gradient budget (c′ ≈ 5.9), and every Bałaban pin.

- **C2b7-1 (MINOR), l.152: accepted, repaired.** "In that passage only (2.37) at 𝕌̃" now reads "In that passage (2.34)–(2.37) at 𝕌̃, as conditions of the class's 𝒟_k, are part of Open (R-eval-curv) (l.158)".
- On the user's instruction (10:00), no further bookkeeping-only re-review rounds are launched. The remaining time goes to the opens' mathematics.

## Open (R-eval-transfer)(b): Reduction to C_H (3 November, 10:00–10:15)

- **Derived to first order, l.130:**
  - V̂ = X^ν with X := e^{iηa″}U_{k+1}. Let U′ be the step-k axial element with X's plain data. Then X = U′^{τ^{−1}} with τ = 1 on 𝔅_k, by REG p.78 l.14 and p.79 l.15. V̂ = U′^{u^{−1}} with Q′_jλ_u = 0 (the linear part of (1.29), p.80 l.26–28).
  - So Q′_jλ_ν = −Q′_jλ_τ on every step-k layer, and R_kΔλ_ν = 0 (residual Landau interpolation, ‖Δλ‖-minimising).
  - |Q′_nλ_τ| ≤ dL^n(1 + 2d)rρ_n, with r ≤ c′(1+β₀)/L, which equals ½(1−β) at the cap.
- **A draft error caught before review.** The first draft took ν's averages from the step-(k+1) axial trees (a flux argument), with ν ∈ N(Q′_{k+1}) ⊖ N(Q′_k). That holds only on Ω_{k+1}. On the old layers ν's averages are nonzero and of a″'s full ratio ½(1−β), so smallness in 1/L alone does not close (b).
- **The fix:** an L-uniform or o(L) constant C_H for the residual interpolation, with c′ divided by 1 + 2d(2d + 1)C_H, so that L ≥ (12d + 6)(1 + 2d(2d + 1)C_H).
- **Still to check:** the current under R(ν), and the second-order terms.
- **Interface obstruction (found 10:10, l.130).** C_H alone does not close (b).
  - At ∂Ω_{n+1} on the top layers (cap binding), λ_τ's averages on the older side have the older room's size, c′ρ_{n+1}.
  - The ‖Δλ‖-interpolation carries their oscillation into Ω_{n+1} over a strip of width O(L^n), where the room is ρ_{n+1}.
  - 𝒟^λ_k's rooms are sharp per layer (CRE (2.39), p.261 l.35–40), with no slack at the top (f_k = 1). A relaxing collar would leave 𝒟_k, since at k − n = 1 it asks for c′ against 1 on Ω_k.
  - The imaginary part of the leak cannot be absorbed into the real U of CRE's existential decomposition, unlike the real part.
  - Remaining routes: show the interface term absent at V̂, or restate the class bounds on a CRE-style existential family that X itself satisfies (U = U_{k+1}). The second still meets VAR (190)'s cross-layer response at the Landau representative, so it is the same obstruction as l.214–216.
- **Same obstruction as the peer's row 226 C_H** (members of members). The peer's 10:12 reduction also leaves "C_H across the scale transitions" open. The table edits crossed (my 197aa5da29e0 → 5692dd639679, with the interface caveat). The peer was told to rebase its row 3 and row 226 edits on 5692dd639679, and I am holding off the table until its SHA arrives.

## (R-eval) Packet TB (Open (R-eval-transfer)(b)'s Reduction), Round TB1: Triage (3 November)

Referee run `referee_cli_20261103-101315_scope_twoloops_RevalTransferB1.json` (10:13–10:27). Two ERRORs and four MINORs. The first-order reduction and the interior C_H arithmetic are confirmed, and so is C2b7-1's repair.

- **TB1-1 (ERROR): accepted.** The interface "obstruction" came only from c′ ∝ L.
  - Checked every use of c′: l.45 (needs c′e^{−δ₀M/16} < 1), l.53 (inclusion, an upper bound), l.54 (the ratio), l.68, l.71 (c′/L ≤ ½), l.166 (c′ ≥ 2), l.225, and row 128's c′^{N₀} ≥ λ, which TB1 did not list. That last one holds for any c′ > 1 because N₀ → ∞ as g → 0 (l.47).
  - So the route takes c′ := 2. The interface term becomes 16dc_dC_H(1+β₀)/L of the younger room, and C_H is stated in an interface form.
  - The dichotomy and the collar route are removed, which also disposes of TB1-6. The l.48 c′ is unchanged, since (b) stays open.
- **TB1-2 (ERROR): accepted.** REG's axial gauge is hierarchical.
  - The averages are iterated one-step staircase averages (Averaging Operations p.24, p.30 (78)), and a level-m link averages fine paths of length growing like ((d+2)/2)^mL^m.
  - My level-by-level curvature recursion gives (1+2d)L² per level, which is not uniform in m. The referee's O(d²) claim is not derived either.
  - So the bound on the averaged links is now a stated input, c_d (c_d = 1 for PRT I's straight-line averages, p.20 l.25), not derived.
- **TB1-3 (MINOR): accepted.** λ_ν = λ_τ − λ_u, and the sign is fixed.
- **TB1-4 (MINOR): accepted.** Pins corrected to l.54 and l.53.
- **TB1-5 (MINOR): accepted.** The wording is now "a constant that grows more slowly than L", and row 226 says "C_H = o(L)".
- **TB1-6 (MINOR):** moot, since the collar route is removed.
- **Table:** f7996e120246 (the peer's rows 3 and 226) → d67bf9e1273c (my row-226 sentences corrected), with the peer notified and told to drop my averages remark.
- **Self-correction:** the 10:10 "interface obstruction" section above is withdrawn by TB1-1.
- **Next:** TB2 launched about 10:35. Cross-reference added to the table (39a4a4739cb3 → 197aa5da29e0, with the peer notified). PRT I Proposition 1.2 gives "d only" constants for the free homogeneous G_k; the multiscale and covariant versions are unproved.

## (R-eval) Packet TB, Round TB2: Triage (3 November)

Referee 10:35–10:48 (`referee_cli_20261103-103456_scope_twoloops_RevalTransferB2.json`): 2 ERROR, 4 MINOR. It confirmed TB1-1 to TB1-6 repaired, and the first-order reduction, the sign, the variational characterisation, the arithmetic inside the layers, and every use of c′ = 2 correct.

- **TB2-1 (ERROR): accepted.** The (1+2d)L² reason contradicted Averaging Operations Proposition 1 (51) (p.26 l.3–8) and p.26 l.11–12: the curvature grows by L² per level. I had found the same independently, before reading TB2. c_d is now derived to first order in l.130.
  - The linear part (p.25 l.29) is the straight path plus loop fluxes.
  - The loops have fewer than (2d+2)L bonds within ℓ¹-distance (d+2)L, and are spanned by the cone of axial staircases in a_dL² plaquettes, a_d = 2(d+1)(d+2).
  - κ_m ≤ L^{2m}κ₀ by (48).
  - φ_m ≤ Lφ_{m−1} + a_dL²κ_{m−1}, so φ_m ≤ L^mφ₀ + 2a_dκ₀L^{2m}.
  - With κ₀ ≤ 2rρ_nL^{−n}, c_d = 1 + 4a_d = 1 + 8(d+1)(d+2). This is cruder than the referee's 4d − 3, but derived line by line.
  - The corrections of the size of U_{k+1}'s curvature times a″ go with the unchecked second-order terms.
- **TB2-2 (ERROR): accepted.** The interface clause could not hold as worded.
  - The input, now C_int, is restated as a sum over layers n = j−1, j, j+1. Each layer contributes L^{−n}δ_n, where δ_n is the largest difference between adjacent averages whose larger block is in layer n; the mismatches are included.
  - With ρ_{n−1} ≤ 2ρ_n, δ_n ≤ 4dc_dL^nrρ_n, so the total is ≤ 32dc_dC_int(1+β₀)ρ_j/L.
  - The conditions become 2(1+β₀)/L ≤ ¼(1−β) and L ≥ 128dc_dC_int(1+β₀)/(1−β).
- **TB2-3 (MINOR): accepted.** Pin changed to l.49.
- **TB2-4 (MINOR): accepted.** The citations are now (15) at p.19 l.45–48, (43) at p.24 l.2–6, and Γ_{c,x} at p.19 l.38–42; (78) is dropped.
- **TB2-5 (MINOR): accepted.** l.73 and l.223 were added to the list of c′ uses.
- **TB2-6 (MINOR): accepted.** Row 226 now names C_int (separate from the peer's vector C_H), gives c_d with its derivation, and names the fourth-order form not covered by Proposition 1.2.
- **Table:** d67bf9e1273c → 3d85a776061d, with the peer notified. The peer then edited line 3 and its own row-226 sentence.
- **Next:** TB3 launched about 10:54 (scope `scope_twoloops_RevalTransferB3.md`).
- **C_int and the peer's lemma (I)** (10:56–11:00, peer triage WILSON_IT1_TRIAGE_LF_GAMMA_2026_10_29.md l.1933–1957, derived there, not reviewed):
  - (I) builds an explicit multiscale interpolant I with prescribed block means on every layer. In the layers it uses quadratic B-splines plus mean-correcting bumps; at the flat interfaces, Hestenes reflection with a cutoff at S′. Its bound is ‖ΔI‖ ≤ C(d)(1 + log L)^{1/2}‖∇f‖, with the log only at checkerboard codimension-2 faces.
  - λ_ν minimises ‖Δλ‖ among gauge functions with its averages (l.130). So for I built at λ_ν's averages, ‖Δλ_ν‖ ≤ ‖ΔI‖: the L² form of C_int follows from (I) with an L-uniform constant up to the log.
  - The construction is local, so I itself has sup bounds of the C_int form. The minimiser λ_ν differs from I by the constrained biharmonic response to ΔI, and that difference is not local without a decay estimate.
  - So the remaining step for C_int is a local (sup) bound for the constrained minimiser: exponential decay of (Q′-constrained Δ²)^{−1} at the rate of the coarsest nearby block, by Combes–Thomas from a per-block gap. This is the same sup step the peer's C_H lacks (peer l.1960: "Combes–Thomas then gives the decay").

## (R-eval) Packet TB, Round TB3: Triage (3 November)

Referee 10:54–11:09 (`referee_cli_20261103-105347_scope_twoloops_RevalTransferB3.json`): 1 ERROR, 1 MINOR. Confirmed: TB2-1 to TB2-6 repaired; the c_d derivation (a_d, κ_m ≤ L^{2m}κ₀ by (48), the recursion, c_d = 1 + 8(d+1)(d+2)); the phase arithmetic and conditions; every use of c′ = 2; every pin. REG's averages are CMP98's (REG p.79 l.11, p.87 l.35–36).

- **TB3-1 (ERROR): accepted.** The gradient half does not follow from any C_int = o(L).
  - Near ∂Ω_j the n = j−1 second differences cost about C_intL^{−2(j−1)}δ_{j−1} ≤ 16dc_dC_int(1+β₀)ρ_jL^{−j}. That is a fixed multiple of layer j's gradient room, because the unit change L cancels r's 1/L.
  - At the bond's own unit, the clause fails for every o(L) constant: alternating ±a layer-(j−1) averages along ∂Ω_j give a counterexample.
  - My check: a″'s layer-(j−1) gradient room bounds the second differences of those averages only by the order of their first differences (adjacent level-m links differ by about L^{2m} times the fine gradient phase). So realisability gives no help.
  - l.130 now limits C_int to the phase half. It states that the gradient half needs either a collar relaxation of layer j's gradient room (width O(L^{j−1}), consumers to be rechecked) or another bound on V̂'s gradient there.
- **TB3-2 (MINOR): accepted.** Row 226 now reads "times a″'s fine phase bound rρ_n" and limits the 32/L cost to the phase half.
- **Table:** dcb15c08e62d (peer line 3) → ade4fd6ebab3, with the peer notified before and after.
- **Status of packet TB:** the reduction (i), c_d, and the phase half are confirmed by TB3 with no defect, which is one clean round for those parts. The gradient half is open.

## Open (R-eval-transfer)(b): The Gauge-Choice Route (3 November, 11:15–11:32)

The obstruction of TB3-1 is a cost of the gauge (memory: gauge first). REG's normalisation (1.29) depends on the generating axial element (p.80 l.29–30). V̂ of the evaluated point and X are normalised from two different axial elements, and ν is the price of comparing them.

- **The route.** The members are G^c-invariant on pairs.
  - For the old terms: U^c_j "is a union of orbits [(𝐔, 𝐉)]" (RG1 p.262 l.11–13, checked), and (1.19) holds "for all G^c-valued gauge transformations u" (p.263 l.36–40, checked).
  - For the words: l.100. The transports enter through the words, whose sup is taken at the representative (l.172).
  - So the class's bound is used at 𝐔″ := 𝐏^{ĥ}, where ĥ has block-point values h and keeps (1.19). By p.79 l.15 and VAR Theorem 1, P(𝐔″) = 𝐔″.
  - With X′ = 𝐏^t, SW (b3)'s Landau point, (1.29) for w = ĥ^{−1}t reads Q′_jλ_t − h = 0 at first order. This uses p.80 l.26–28 and Q′_jλ_ĥ = h for ĥ covariantly constant along the trees.
  - h := Q′_jλ_t solves it, and the implicit function theorem gives the nonlinear version. REG Theorem 4 then makes X′ the VAR representative of 𝐔″.
  - The pair is (𝐔″, R(ĥ)𝐉), whose Landau form is (X′, R(t)𝐉).
- **What changed in the note.**
  - The C_int and c_d reduction is dropped from l.130, together with the route's c′ := 2. l.48's c′ is unchanged.
  - (b)'s status was propagated at l.8, l.130 (twice), l.136, l.154, l.159, l.166, and l.172.
  - Row 226 now carries one sentence (4baf32c0ae4f, with the peer notified before and after). The note's other c_d (l.338, the tail bound) is unrelated.
- **Self-check before review.** The current must transform with the configuration's transformation, so R(h̃)𝐉 was corrected to R(ĥ)𝐉, with h̃ := ĥ.
- **Next:** TB4 on the new (b) passage.

## Open (R-eval-transfer)(a): Base 𝐕 (3 November, 11:36–11:48)

- **Premises read.**
  - RG1 (3.21)–(3.27), pp.274–275: Bałaban deforms the localized background U_{k+1}(□₀, M·(𝐔)) by 𝐇_k and then re-projects with U_j(□₀, M·(·)). He never claims that the deformed point is a minimiser.
  - CRE (2.2), (2.11)–(2.15), pp.255–256, gives the determining sets and their localization.
  - LFR II (1.33), p.365: the post-R set 𝐁_k is coarser than 𝐁_k″.
  - VAR Proposition 9, p.309.
- **The route.** The Proposition 9 comparison of *At s ≠ 1* uses 𝐕 itself as its base, at every s.
  - 𝐕 is fixed by each member's P. 𝐁_{k+1}″ is the T-step's coarsening of 𝐁_k, which is coarser than 𝐁_k″, so the nesting argument (l.133) applies with 𝐁_{k+1}″(Y′). The complex points follow by the identity principle.
  - P of the point is e^{iη𝓗}𝐕 with |𝓗| ≤ K sup|𝐇|. This is below the response 2K sup|𝐇| at s ≠ 1, so l.137–138's budget holds with all of 𝓗 counted as response, inside the margin ½(1−β)α_{1,k} that 𝐕's own data leave (l.54).
  - The real base is U_{k+1}, the T-step's real point at tB′ = 0 at a global background, which l.159 covers.
  - The curvature conditions at P of the point join Open (R-eval-curv)'s list, as they already do at s ≠ 1.
- **Status propagated** at l.6, l.7, l.8, l.32, l.38, l.131, l.154, l.159, l.166, l.172, l.213, and l.218, in the D2.7 closure (l.3, l.5, l.7), the continuum closure (l.3, l.5), and map l.342. The old route (collar width against (190)'s decay) is dropped.

## (R-eval) Packet TB, Round TB4: Triage

The referee ran from 11:32 to about 11:48. It found one GAP and three MINOR findings. The route's mechanics were confirmed: ĥ exists and is entire in h; \overline{R₀ĥ}^j = h holds exactly by CMP98 (78)–(80); the IFT is pointwise; R_k = R_kR_{k+1}; and all pins match.

- **TB4-1 (GAP): accepted.** The G^c-invariance of the members is Bałaban's assumption for 𝐄^{(j)} only (RG1 p.263 l.34). The post-R extensions, the words, and the covariant members are not covered by it.
  - **Repair.** No complex invariance is used. At real parameters (real 𝐕, s, t, and B′), t, h, and ĥ are G-valued. The members are G-invariant at real configurations: Bałaban's spaces are G-invariant (LFR I p.191 l.32–33), his effective action is gauge invariant (LFR II p.378), U_k^0 is G-covariant by the minimal orbit (CRE (2.12)), and the words are traces of holonomies. The step-(k+1) member is therefore defined at the new pair, and it equals the T-step's integrand at real parameters.
  - The T-step uses complex parameters only for the analytic extension in its Cauchy bounds, and that extension is unique. There is no continuation in the gauge variable, as at l.111.
  - Covariant members (B-terms, D2.6 5.4's transports) become ĥ(x)^{−1}Y(𝐔″)ĥ(y), with a factor of at most e^{2|Im λ_ĥ(x)|+2|Im λ_ĥ(y)|}. This factor is added to Open (R-eval-curv) (l.6), next to l.153's B-term transfer.
  - The statuses at l.8, l.130, and l.159 and row 226 now say so (table b9e4305e9394 → ada9a194f7c9, with the peer notified before and after). The peer's S9 used the G^c-invariance itself and is being moved to the identity-principle form.
- **TB4-2 (MINOR): accepted.** The action is on the left, so w := tĥ^{−1}, and (1.29) is imposed on w^{−1} (REG p.81 l.11–15). The first order is unchanged.
- **TB4-3 (MINOR): accepted.**
  - |λ_t| is bounded at the block points by REG's (1.70)–(1.72) reasoning, as at l.106, by O(L^iη(h_k + α_{1,k})). Hence |h| ≤ |λ_t|, M(𝐔″) stays inside VAR's radius, and the IFT applies.
  - Theorem 4's hypotheses were read (p.82 l.33–37, p.87 l.47–49) and checked at 𝐔″. Theorem 4 and VAR Theorem 1 are applied at real parameters and extended by the identity principle.
  - The construction is stated per member, with that member's set (block points, (1.19), (1.29)). The Landau condition for a finer set follows from that for a coarser one.
- **TB4-4 (MINOR): accepted.** X′'s second-order formula is now restricted to s = 1 at a global background. At s ≠ 1, and at a localized background, X′ includes l.137's response or part (a)'s 𝓗.
- **Next:** TB5 on (a) and the repaired (b).

## Open (R-eval-old) and Open (R-eval-curv): Work During TB5 (3 November, 12:00)

- **(R-eval-old): reduced, still open.** The third input of l.5 needs the sup-norm response constant C_{resp,∞}. That constant is the large-field note's C_H at i′ = 0 (LF l.6: abs(Q_{i′}HB) ≤ C_HL^{−(i−i′)}abs(B), in the units of the data), for the same minimisers. λ absorbs C_HM⁵ (l.73, l.166), and Λ lies on the layers where λ^{(k)}_n = λ.
  - The peer (12:00) reports that C_H is not derived. The pointwise bound next to Λ^c is open, the gradients may lose a power of L at re-entrant corners, and the field bound needed here still lacks the layer term of T.
  - The peer's bound needs a VAR-regular real base. U_k^0(M(U)) is regular only on the squares of P^c in LFR I (1.88) (curvature of (1, V_h) below ½ε_h(L^{k−h}η)², p.197 l.44–51), not on P.
  - l.5 now names the two remaining inputs: the field bound, and the terms with P ≠ ∅.
- **(R-eval-curv): candidate route, not yet written into the note.** Use the Schwarz lemma in the complex part of the data.
  - The curvature quantities of 𝕌^{(0)} are analytic in the data. They are bounded by f_n times the room wherever LFR II (1.65) lands, and at real data they are o(1) times the room ((1.48), LFR I p.186 l.35–43).
  - At points whose complex part is at most 1/8 of a balanced domain on which (1.65) holds, they are at most (1/4 + o(1))f_n times the room. That is below f_n − ½β2^{−(k+1−n)}, which gives the margin.
  - It doesn't work: dilating the complex part breaks the input's own (2.34)–(2.37), since the gradient room allows η²|∇A′| up to 2λ_R times the curvature room (l.6), and the T-step's inputs take their curvature from the base e^{iηa″}U_{k+1}, not from a small complex part (map l.928).

## (R-round) and (R-att-ext): Pre-Checks for Round 2 (3 November)

Scopes: `scope_twoloops_Rround2a.md` ((R-round) block and (6B) *The count*, l.681–712), `scope_twoloops_Rround2b.md` ((6B) l.713–756 and (6C) l.819–822, l.840–850), and `scope_twoloops_Rattext2.md` ((R-att-ext) block, (6C) l.784–790 and l.823–839).

- **The arithmetic was recomputed.** The units (16.1 + 0.23σ, 17 + σ/4, the threshold 22, 2^{d+1} + ½ + 16 ≤ 2^{d+2}); the payment (6.3C_Ψ′M, 182C_Ψ′Mε_k ≤ ν_r); the joins (4.2/34 ≤ 1/8, 160MC_jne^{−p₀/2} ≤ c_F, (21/4)MC_jnε_k²); the first case (20/168 ≥ 1/9); (6C)'s units (21/4 ≤ 16/3); D's budget (0.858 + 3ε_k/4 ≤ 0.89); the 15.7 re-run (R_k² ≥ 440/ν_r, 880/ν_r, R_k ≥ 17/ν_r); the u = 16 and u = 19 conditions (0.1446 ≤ 0.145, 0.2344 ≤ 0.235); and the attached weights (9/32, 9/64, a budget of 0.914 ≤ 1). All hold.
- **One wrong reason, repaired.** (6C) *The extent* (l.826) paid its constant (ν_r/8)(2R_k + 1) by a margin, on the grounds that "every polymer of the R-gas has a first-class component in its localisation domains (p.389 l.27–28)". p.389 says only that a localisation domain contains a second-class Y_i or is disjoint from them, with q ≥ 1 first-class components in the second case. The margin is now taken from a first-class component of g, which every group has, since its slots are arc words of first-class components or insertions whose 𝒦 consists of first-class components. This is *The weights*' reason (l.788; D2.7 15.3, 15.5(i)).
- The LFR II and CRE pins of (6B)'s *The payment* (p.376 l.11–13, p.368 l.23, CRE p.250 l.47–48, p.251 l.39–40, p.268 l.41) match.
- **(R-eval-cr) P2 and (R-member) P1 scopes refreshed.** The line numbers are now the current ones (block l.211–223, *Where it lands* l.44, the family l.45–67; (R-member) l.232–263), and P2 checks against the corrected files. In (R-eval-cr) l.221, three raw-file pins were converted: LFR II p.378 l.28–29 → l.27 ("any component of the first, or of the second class"), p.366 l.24–28 → l.25–27 (U_k^c(Z, α_{0,k}, α_{1,k}) and its bounds), and p.379 l.28–32 → l.27–31 (the first-order bound).

## (R-eval) Packet TB, Round TB5: Triage (3 November, 12:20–12:40)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB5.md`. Verdict: not clean, with one gap (TB5-1) and five minors. TB4-1, TB4-2, and TB4-4 were confirmed repaired, and TB4-3 partly. All six findings are accepted and repaired in the note's l.130, l.6, l.8, l.38, l.154, l.159, and l.213, and in table row 226 (peer protocol: base b821b83673f7, new SHA 0e56bbcdffc8).

- **TB5-1 (GAP): accepted, repaired by a new construction.**
  - The finding: REG (1.70)–(1.72) bound only the normalised transformation. By CMP98 (84), t's block values carry the factor \overline{R₀t^{−1}}^j, whose linear part is −h, so "|h| ≤ |λ_t|" was circular, and λ_t was bounded at the block points only.
  - The repair: the pair is chosen from the background alone, and no transformation from 𝐏 is bounded. CMP98 (72), (77), (84), and (86)–(87) (p.29–31) give, for any configuration U₁ near the base, real or complex, exactly one transformation u with U₁^u axial and REG's normalisation, as an explicit function of U₁ ("uniquely determined by all the conditions", p.31 l.20). REG uses it layer by layer (p.88 l.36), and (1.70)–(1.72) bound it at every point of Ω₀.
  - v_k and v_{k+1} are this transformation for X = e^{iηa″}U_{k+1} with the step-k and step-(k+1) sets. 𝐕 = X^{v_{k+1}} by the same uniqueness, 𝐕_X := X^{v_k} = 𝐕^c with c := v_kv_{k+1}^{−1}, and |λ_c| ≤ a_c = O(α_{1,k}) at every point.
  - h := c at the block points, and ĥ keeps (1.19), so |λ_ĥ| ≤ a_c at every point (the recursion conjugates by the real base). 𝐔″ := 𝐏^ĥ has the data M(𝐏)^h = d_{𝐕_X} ⊕ δ^h.
  - X is 𝐕_X's representative by Theorem 4's uniqueness, and so 𝐔″'s representative is exactly e^{iη(a″+𝓗^h)}U_{k+1}, with 𝓗^h the (190) integral of l.165 at d_{𝐕_X}. No implicit-function step is used.
  - t := u″^{−1}ĥ is bounded at every point, and R(t)𝐉 differs from the step-(k+1) frame current by a factor e^{2|Im λ_f|} = 1 + O(α_{1,k}).
  - The factor e^{2a_c} on δ fits the room of l.138's inequalities: (3/16)(1−β) against ¼ on the top layers, and ⅛(1−β) against ¼(1−β) on the older ones.
  - Status: derived, awaiting review (TB6). The status sentences at l.8, l.130, l.159, and row 226 now describe this construction.
- **TB5-2 (MINOR): accepted.** The factor is now ‖π(ĥ(x))^{−1}‖‖π(ĥ(y))‖ ≤ e^{c_π(|Im λ_ĥ(x)|+|Im λ_ĥ(y)|)} ≤ e^{2c_πa_c}, with e^{4a_c} for the adjoint-valued B-terms. l.6 now lists the Cov(k) members.
- **TB5-3 (MINOR): accepted.** The outer fields enter as R(ĥ)ω (Cov(k), map l.622). Their domain must absorb Ad(ĥ), which needs the enlargement e^{2a_c}; this is filed with the covariant factor under Open (R-eval-curv).
- **TB5-4 (MINOR): accepted.** Theorem 4's uniqueness is now used at 𝐕_X, and its conclusions are checked for X:
  - (1.38) by R_k = R_kR_{k+1};
  - (1.62) as the Ω_j, j ≤ k, part of (1.62) at step k+1, with REG's α's taken as the larger of the two steps' values;
  - (1.37) by CMP98 (88).
  - The hypotheses, (1.66) included, hold with α₁ + 2a_c.
- **TB5-5 (MINOR): accepted.** Part (a) now compares relative to the real base U_{k+1}: 𝓗 := 𝓗_S(d_𝐕 ⊕ δ) − 𝓗_S(d_𝐕) = ∫₀¹κ(B_w)∂_wB_w dw, with (190) uniform on the ball as at l.164–165. The bound becomes (1 + O(α_{1,k}))K sup|𝐇|, below 2K sup|𝐇|.
- **TB5-6 (MINOR): accepted.** The exception lists at l.38 and l.213 now include (2.34)–(2.37) at P of the re-projected points and the conjugation factors at part (b)'s pairs. Row 226 now says "G-invariant" for the invariant members and names the G-covariant ones separately.

**Next:** TB6 on (a) and the new (b).

## (R-eval) Packet TB, Round TB6: Triage (3 November, 13:03–13:05)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB6.md`, 12:40–13:03. The new (a) and (b) are correct line by line. The checked items are the CMP98 uniqueness, REG's pointwise bounds on v_k, v_{k+1}, u″ and ĥ, M(𝐔″), Theorem 4's hypotheses and conclusions for X, the identity principle, the (190) integral, the fit in l.138's budget, the status sentences, and every checked pin. TB5-1 to TB5-6 are confirmed repaired. One MINOR finding.

- **TB6-1 (MINOR): accepted, repaired.**
  - The finding: 𝒟^λ_k's current condition is on 𝐉 − J_k (l.51), but l.130 and l.154 bounded |R(t)𝐉| only. The term (R(f) − 1)J_k was missing, and it is present already at real parameters.
  - The repair at l.130: R(t)𝐉 − J_k = R(f)(R(v_{k+1}^{−1})𝐉 − J_k) + (R(f) − 1)J_k. On layer n, |λ_f| ≤ C_fdλα_{1,k}L^{n−k} by (1.70)–(1.71), as at l.106, and (L^nξ)³|J_k| < α_{0,n} by CRE (2.36) at the real base (p.261 l.19).
  - α_{0,n} ≤ (1+β₀)α_{0,k} for n ≤ k, since g_n ≤ (1+β₀)g_k (CRE (2.6), p.255) and x(log x^{−2})^{q₀} is increasing for small x.
  - So the term is O(dα_{1,k}) times l.51's room, uniformly in n and K. l.154 now names the term.
- **The remark (not a finding):** the covariant and outer-field factors must not compound over the steps, since Σ_kα_{1,k} is not uniform in K. This is now stated at l.6, under Open (R-eval-curv).

**Next:** TB7, for a second pass and to check the TB6-1 repair.

## (R-eval) Packet TB, Round TB7: Triage (3 November, 13:19–13:27)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB7.md`, 13:05–13:19. The TB6-1 repair is confirmed: the identity, the norm bounds, and the pins (CRE (2.36), (2.6), (2.28)). l.6's compounding sentence and the second pass over (a) and (b) are correct. One MINOR finding, which is a real gap, so the clearance rule calls for another round.

- **TB7-1 (MINOR): accepted, repaired.**
  - The finding: |λ_f| ≤ C_fdλα_{1,k}L^{n−k} does not follow from the stated bounds. v_{k+1} is normalised for 𝐕's coarser set, and ĥ was bounded only by a_c.
  - Checked: REG (1.19) (p.79 l.4–9). The member's chains at a point are the first levels of 𝐕's chains there, since its layer index is at most 𝐕's. So 𝐕 and 𝐕^c are both axial for the member's set, c keeps (1.19), and ĥ = c.
  - So f = u″^{−1}v_k, and both factors are normalised for the member's set. (1.70)–(1.71) (p.88 l.37–61) bound each on layer n by Σ_{m<n}4dL^{m+1}φ ≤ 8dL^nφ.
  - l.130 now states ĥ = c in *The pair* and the bound on f in the current paragraph.
- **The remark on CRE (2.36) at the real base: made an open, Open (R-eval-Jbase).**
  - The membership of (U_k, J_k) in (2.36) is what D(k)(iii) evaluates at (map l.316). It is not among the base-point conditions that map l.315 and note l.173 derive.
  - Bałaban builds the minimiser's current into his spaces (RG1 (3.40), p.278; REG 𝔘_k(α₀), p.86 l.5–6). RG I p.263 l.21–22 states it for single-scale minimal configurations of small curvature. The multiscale bound is not printed.
  - Route: on the support, the real base's curvature is at ε_n-level (χ_k, and χ_{h,1/2} of LFR I (1.88)), with ε_n/α_{0,n} = (A₀/α₀)(log g_n^{−2})^{p₀−q₀} → 0 (q₀ > p₀). The minimiser's current is the multiplier term Σ_jQ_j*Λ_j(L^jη)^{−3}B₁ of REG (1.58), bounded in the (−3)-norm by PBG Theorem 3.3 linearly in the data, at ε-level.
  - Status lines l.8, l.38, l.154, l.159, and l.213 now name it.
  - **Route being derived (13:30–13:40; to go into l.130 after TB8, not during it):**
    - VAR Theorem 1 (p.279 l.8–12) puts the minimal orbit in 𝔘_k({Ω_j}, B₃ε₁). Its definition (VAR (2), p.278 l.2–8) includes |D*_U∂U| < ε₀η²(L^jη)^{−3} on Ω_j. With J = D^{ξ*}ξ^{−2}π Im∂U and R(U) commuting with π Im, this gives (L^jξ)³|J| < B₃ε₁ on layer j.
    - A global ε₁ does not suffice, since ε₁ is the maximum over all layers and g_k/g_n is not bounded uniformly. So localise. Near a bond b on layer n, U_k equals its localised minimiser U(𝐁_k(Ω), M(U_k)) up to a gauge transformation, by l.130's identity on minimisers, with Ω a neighbourhood of b. CRE applies VAR to every determining set (p.256 l.48–53).
    - Ω meets only layers m ≤ n + 1, since dist(Λ_n, Ω_{n+2}) ≥ RML^{n+1}ξ (PRT II (2.2)). CRE (2.6) gives g_m ≤ (1+β₀)g_n for m < n, and g_{n+1} ≤ (1+β₀)g_n (its first line at n − m = 1). So ε₁ ≤ Cε_n on Ω, and (L^nξ)³|J_k(b)| < B₃Cε_n < (1−β)α_{0,n} for g small, uniformly in n and K, since ε_n/α_{0,n} = (A₀/α₀)(log g_n^{−2})^{p₀−q₀}.
    - Premise still to check: VAR (7) at ε₁ = Cε_n on Ω, including the pinned bonds of Γ₀. This needs the base's curvature at ε_m-level on layer m (Cε_mL^{−2m} per fine plaquette). The old layers of Λ have it by LFR I (1.91)/(1.95) (l.5), and the top layer by χ_k. A citation for every layer of the support is still needed. Map l.315's real-U (2.34) is only α-level, and α_{0,m}L^{−2m} vs ε_n does not close.
    - Source for that premise (13:40): LFR I (1.3)–(1.4) (p.178 l.15–22), the per-layer indicators on Z, sup_{p⊂□^∼}|U_{j,□}(V_j, ∂p) − 1| < ε_j(L^{k−j}η)² = ε_jL^{−2j}, in VAR's scaling. Their transfer to the post-R configuration is Bałaban's (1.89)–(1.95) argument (p.198–199). It is explicit on layer h, with H_{h,□} bounded by αε_h, and the other layers are by "reasonings of this type" (p.198 l.17–18). That is his presented-as-true claim, accepted. Still to check: the base points on the components excluded from Z (new large fields), where (1.3)–(1.4) are not imposed. Write-up into l.130 after TB8 returns.

**Next:** TB8 on the TB7-1 repair, the R-eval-Jbase sentences, and (b).

## (R-eval) Packet TB, Round TB8: Triage (3 November, 13:38–13:40)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB8.md`, 13:25–13:38. The TB7-1 repair is correct line by line: 𝐕 is axial for the member's set, the member's layer index is at most 𝐕's, c keeps (1.19) so ĥ = c, f = u″^{−1}v_k, and the L^{n−k} decay follows, consistent with the rest of (b). Open (R-eval-Jbase) is confirmed a genuine gap, with its pins matching. Three MINOR findings, none a gap in the mathematics (status labels, the statement of the open, and a constant with no downstream effect). So under the clearance rule this is **TB's first clean round**, with the minors repaired.

- **TB8-1 (MINOR overclaim): accepted, repaired.** R-eval-Jbase was missing from (b)'s own status, from "Both parts … derived below", and from l.7 and l.785. All four now name it.
- **TB8-2 (MINOR): accepted, repaired.** The open is now stated once, in its weakest form, as (L^nξ)³|J_k| ≤ C_Jα_{0,n} with C_J fixed before g. (2.36) at (U_k, J_k) gives C_J = 1. The frame term is O(C_Jdα_{1,k}) times the room, and l.38, l.154, and l.213 use the same wording.
- **TB8-3 (MINOR, no effect): accepted, repaired.** Checked against REG p.88: (1.70)'s factor 2 times (1.71)'s 4dL^{m+1}φ gives Σ_{m<n}8dL^{m+1}φ ≤ 16dL^nφ. Corrected. C_f is absolute, and a_c's 33d is unaffected.
- Not checked by TB8: CRE (2.14) on p.257 (layer-by-layer union), and LFR I p.179 (the step-(k+1) set before its R-operation). Both go into TB9's source list.

Pre-check before TB9: CRE (2.14) (p.257 l.13–15) is a union region by region, 𝐁 on Ω^{∼−2} and 𝐁_j(Ω) on the collar. With the monotonicity of maximal domains that TB8 checked, the member's layer index is at most 𝐕's in the collar too.

**Next:** TB9 (launched 13:40, `scope_twoloops_RevalTransferB9.md`), a pure second pass on TB with no new mathematics in its passage. JB (Open (R-eval-Jbase)) follows as its own packet.

## (R-eval) Packet TB, Round TB9: Triage (3 November, 14:04–14:17)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB9.md`, 13:40–14:03. TB8's three repairs are correct. The full second pass confirms CMP98's uniqueness (also for G^c-valued u), 𝐕 = X^{v_{k+1}}, (1.70)–(1.72) at every point, ĥ = c through CRE (2.14)'s strips, M(𝐔″), Theorem 4 at 𝐕_X and 𝐔″, the (190) integral, l.138's room, the frame algebra, the covariant factors, and every checked pin. There were three MINORs and no ERROR. TB9-1 is a real gap, so **TB9 is not clean** and TB10 follows. TB8 remains TB's one clean round.

- **TB9-1 (MINOR, a real gap): accepted, repaired.**
  - Part (a) gave the T-step's coarsening Bałaban's name 𝐁_{k+1}″. In LFR I that name belongs to the R-operation's set, built from the domains Ω″_j of (1.12) (p.179 l.32–45). The set the R-operation starts from is (1.14)'s (l.59–62).
  - Part (a)'s conclusion survives, with one more link. The preliminary integrations only coarsen (l.75; (1.12)–(1.16)), so Bałaban's 𝐁_{k+1}″ is the T-step set 𝐁^T_{k+1} or coarser. The members' sets are therefore finer than 𝐕's either way.
  - l.131 did not survive. Its P_{k+1}(U_{k+1}) = U_{k+1} holds by nesting only where 𝐁_{k+1}″ = 𝐁^T_{k+1}, that is, where the (k+1)-th R-operation has no region Z ((1.12) with Z = ∅). The minimiser of a finer set is not the minimiser of a coarser one.
  - Repair: part (a) now names 𝐁^T_{k+1} and states the relation. It also states that the same comparison serves a global background with a region Z. l.131 is restricted to the case without one.
- **TB9-2 (MINOR, wording): accepted, repaired.** The sentence on REG's interpolation between the two normalisations now names the frame term (R(f) − 1)J_k. That term is first order, present at real parameters, and bounded by λ_f's layer decay.
- **TB9-3 (MINOR): accepted, repaired.**
  - The open is now stated in the form the step uses: B_J := sup_n(L^nξ)³|J_k| → 0 as g → 0, uniformly in k and K. The frame term is at most 3C_fdλλ_RB_J/(1−β) times l.51's room (α_{1,k} = λ_Rα_{0,k}; f_nλ^{(k)}_n ≥ 1 − β by l.48).
  - Why o(1) and not a constant bound fixed before g. l.54 splits the room as ¾(1−β) and ¼(1−β), and the frame term must fit in the slack of that split. The constant B₃ε₁ that the note already has at the base (l.94, l.101) is fixed with M′ε₁ ≤ a₁, and its order relative to λ and λ_R has not been traced.
  - The route is now written into l.130. The base is VAR's minimal configuration. For every ε₁′ ≤ ε₁ at which its data meet VAR (7), Theorem 1 gives a minimal orbit in 𝔘_k({Ω_j}, B₃ε₁′) (VAR (8), p.279 l.13–14). This is the base's orbit by the uniqueness clause in VAR's space (6) with ε₀ := B₃ε₁ (B₃ε₁′ ≤ ε₀ ≤ B₃a₁ ≤ a₀). VAR (2)'s second line (p.278 l.6) and (28) (p.282 l.34, J = Im η^{−2}D*∂U) then give B_J ≤ B₃ε₁′.
  - What remains is a (7)-level ε₁′ → 0 for the real base's data on all of 𝔅_k. CMP98 Proposition 2 (p.26 l.46–53) is local and assumes curvature only ((52), l.14). It turns the base's own curvature into (7). But the real-U part of CRE (2.34) is posed only for n ≥ 1 (CRE p.261 l.20: n = 1, …, j − 1, and Ω_j). The pinned layer Γ₀ = Ω₁^c is not covered.
  - VAR p.278 l.46–47 (ε₁ = O(ε₀) "if the space (6) is non-empty") is circular as a source, because (6) includes the current.
- l.38, l.154, and l.213 restated in the same form.
- Remark (not a finding): CRE p.261 l.60–62 makes CRE's B-terms invariant scalars, so e^{4a_c} overestimates them harmlessly. No change.

**Next:** TB10 (launched 14:17, `scope_twoloops_RevalTransferB10.md`). JB: find the (7)-level of the real base's data on Γ₀ = Ω₁^c and on the mixed block plaquettes (VAR p.278 l.38–45). The draft is in `WILSON_IT1_JBASE_DRAFT_2026_11_03.md`.

## (R-eval) Packet TB, Round TB10: Triage (3 November, 14:32–14:34)

Referee: `claude -p` on .claude-Main, scope `scope_twoloops_RevalTransferB10.md`, 14:17–14:31. The referee confirmed the following:
- TB9-2's and TB9-3's repairs.
- LFR I (1.10)–(1.17): the R-operation only coarsens, so 𝐁_{k+1}″ ⪰ 𝐁^T_{k+1} ⪰ 𝐁_k ⪰ 𝐁_k″.
- The frame-term ratio and the VAR Theorem 1 route to B_J ≤ B₃ε₁′.
- Every checked pin.

There were two MINORs, both caused by my TB9-1 repair. TB10-1 is a real gap (the base was not identified), so **TB10 is not clean**. TB8 remains the one clean round.

- **TB10-1 (MINOR, a real gap): accepted, repaired.**
  - My TB9-1 repair restricted l.131 to the case with no step-(k+1) region Z. It also said RG2's identity was "not available" otherwise. That was false.
  - At real 𝐔, P_{k+1}(𝐔) is a 𝐁_{k+1}″-minimiser. By the nesting argument, a minimiser of a coarser set is fixed by the projection of a finer one. So it is also the 𝐁^T_{k+1}-minimiser at its own averages, which makes it a T-step background.
  - TB9-1's worry applies only to a T-step minimiser at prescribed T-step data. Such a minimiser is not in 𝓜_{k+1} when Z ≠ ∅, so it could not have been 𝐕's real base.
  - Repair: part (a) has a new paragraph, *The real base*. U_{k+1} is Bałaban's post-R background at step k+1 (LFR II (1.33)–(1.35) at k+1; l.159). Its set equals 𝐁_{k+1}″ off Z and Z^{(k+1)} on Z, so it is coarser than every step-(k+1) projection's set. It is therefore fixed by every P_{k+1}, and it is a T-step background at its own data, with or without Z.
  - l.131 is restored at every global background, and V is named as U_{k+1}'s T-step data. The false sentence is deleted.
- **TB10-2 (MINOR): no change needed.** With l.131 holding at every global background, the status sentences (l.8, l.154, l.159, (b)'s 𝓗^h sentence, (a)'s heading) are correct as written. The referee says so in the finding.
- **Remark (constant bound):** the referee repeats TB9-3's point that B_J ≤ c(1−β)²/(C_fdλλ_R), fixed before g, would suffice. The o(1) form is kept, and it is not a false statement. It is what the route gives once the (7)-level tends to 0. The constant's fit in l.54's slack would need the 𝐇-part's share traced against l.137.

**Next:** TB11 (launched 14:33, `scope_twoloops_RevalTransferB11.md`). If TB11 is clean, it is TB's second clean round (TB8, TB11).

## (R-eval) Packet TB, Round TB11: Triage (3 November, 14:47–14:56)

TB11 returned at 14:46 (`referee_cli_20261103-143351_scope_twoloops_RevalTransferB11.json`) with no ERROR and two MINORs. Both are gaps in the argument, not wording, so under the clearance rule TB11 is not clean. TB has one clean round (TB8).

- **TB11-1 (MINOR, real gap): repaired.**
  - The TB10-1 repair named U_{k+1} as the post-R(k+1) background. l.131 then showed RG2's identity only there. When Z ≠ ∅ those points are a lower-dimensional part of 𝓜_{k+1}, so the identity did not extend to 𝓜^c_{k+1}.
  - *The real base* now makes U_{k+1} a real point of 𝓜_{k+1}. Every real point is a 𝐁_{k+1}″-minimiser, and 𝐁_{k+1}″ is 𝐁^T_{k+1} or coarser. So by nesting every real point is fixed by every P_{k+1} and is a T-step background at its own data, with or without Z. Bałaban's post-R(k+1) background is named as one such point.
  - l.131 now states RG2's identity at every real point 𝐕 of 𝓜_{k+1}, with V the T-step data of 𝐕. It extends from 𝓜_{k+1}, a totally real submanifold of maximal dimension, to 𝓜^c_{k+1} and complex t. The V-clash is gone, since *The real base* no longer writes the post-R data as V.
- **TB11-2 (MINOR, real gap): repaired.**
  - The claim was that U_{k+1}, the T-step point at B′ = 0, is covered by l.159's post-R base. Nothing puts B′ = 0 on the support of the R-step's indicators.
  - Repair: part (a) has a new paragraph, *The base on the support*. At both a global and a localized background, l.159's bounds take as real base the real T-step point at the integration variable, U^{B′} := U_k(e^{iB′}V) = e^{iη𝐇(1,B′)}U_{k+1} (l.131 at the real point U_{k+1}).
  - U^{B′} is the post-R background at the datum e^{iB′}V (l.133). The T-step integrand carries the post-R function at that datum with its indicators as factors, so wherever the integrand is nonzero, e^{iB′}V is on their support.
  - The whole deviation from U^{B′} counts as the complex part, as at l.167 (the extension-domain points). That deviation is a″ + X − 𝐇(1,B′), where:
    - X = 𝓗^h at a localized background;
    - X = 𝐇_𝐕(1,tB′) plus *At s ≠ 1*'s response at a global one.
  - Beyond a″ it is at most (2 + 2K)h_k^{(K)} on the top layers. That is at most (1−β)min(β,1)α_{1,k}(1+K)/(8K) + O(Kε_k) ≤ min(β,1)α_{1,k}/4, for K ≥ 1 and g_K small under q₁ > p₀.
  - On an older layer it is at most 2Kh_k^{(K)} + 2·O(1)(Lθ)^{k−m}h_k^{(K)} ≤ ⅜(1−β)α_{1,k} + O(ε_k). This is inside SW (b3)'s margin ½(1−β)α_{1,k}, using l.138's two bounds.
  - The current condition is on the point's own current and does not change.
  - l.159 now cites *The base on the support* for both backgrounds. Its old wording, "l.137's choice of base at a global background", named no base at a global background.

**Next:** TB12 (`scope_twoloops_RevalTransferB12.md`). If TB12 is clean, it is TB's second clean round (TB8, TB12).

## (R-eval) Packet TB, Round TB12: Triage (3 November, 15:10–15:25)

TB12 returned at 15:09 (`referee_cli_20261103-145534_scope_twoloops_RevalTransferB12.json`) with no ERROR and three MINORs. It confirmed the TB11-1 repair and the arithmetic of the TB11-2 repair. TB12-1 and TB12-2 are gaps (a missing term, an unbounded transformation), so TB12 is not clean. TB has one clean round (TB8).

- **TB12-1 and TB12-2 (MINOR, real gaps): removed by withdrawing the base change.**
  - Both came from TB11-2's move of l.159's base to U^{B′}.
    - TB12-1: the centre J_k of 𝒟^λ_k's current condition moved, and that shift's term was in no budget.
    - TB12-2: part (b)'s exact pair is built relative to U_{k+1}, while l.163 reads 𝓗(Δd) at V̂ relative to l.159's base. The G^c transformation w between the two representatives was not bounded. REG prints no dependence of its representative on U₀ (Theorem 4, p.88, gives uniqueness only).
  - Repair: the base stays U_{k+1} at both backgrounds. The new paragraph *The base near the support* replaces *The base on the support*. l.159's chain uses the support at the base only through the bound on δ^{re} (l.160), and U_{k+1}'s data lie within sup|B′| ≤ 2C₁^{RG2}O(1)ε_k (l.138) of the datum e^{iB′}V. That datum lies on the support wherever the T-step's integrand is nonzero (RG1 (2.1), (2.9), p.265 l.30–39).
  - δ^{re} at a base is U's data minus the averages of U_0^{(AL)}, a function of U's data off Λ. Along the segment between the two data:
    - the critical extension moves by at most C_{rsp}M⁵sup|B′|, by LFR II (1.38)–(1.42), p.366 l.30–p.367 l.24, with (1.41)'s 4d(100M)⁵γ₀^{−1}B₃² = C_{rsp}M⁵, in the axial gauge of (1.38);
    - U_{k,Z}'s averages move by at most K(1 + C_{rsp}M⁵)sup|B′|, by VAR Proposition 9 and (190).
  - So at U_{k+1}, |δ^{re}| ≤ O(B₃M₀ + Kd² + KC_{rsp}M⁵C₁^{RG2})ε_k, with a constant fixed before g. C_{mx} carries the new term in l.45, l.160, and table row 128 (table 89C8CA59D1D6 → 854857651677, peer notified).
  - Part (b)'s pair and the current's centre are relative to U_{k+1} throughout, so neither TB12-1 nor TB12-2 arises.
- **TB12-3 (MINOR, pin and qualifier): repaired.** The post-R identification of U^{B′} now cites l.132, and "up to a G-valued gauge transformation (RG1 (2.6))" is kept.

**Next:** TB13 (`scope_twoloops_RevalTransferB13.md`). If TB13 is clean, it is TB's second clean round (TB8, TB13).

## (R-eval) Packet TB, Round TB13: Triage (3 November, 15:17–15:36)

Referee result: `referee_cli_20261103-151748_scope_twoloops_RevalTransferB13.json`. No ERROR, GAP, or OVERCLAIM. TB12-1 and TB12-2 are resolved, and TB12-3 is repaired. *The base near the support* is correct in substance: U^{B′} is the post-R background, the integrand vanishes off the support, the bound on sup|B′| holds, and LFR II (1.41) applies, with exact pins. l.159–166 use the support only through δ^{re}. Two MINORs, both real gaps (a missing constant and a wrong Lipschitz factor), so TB13 is **not clean**.
- **TB13-1 (MINOR): repaired.** C_{mx}'s definition at l.45, the base-change coefficients at l.161, and T₂'s bounds at l.165 now carry + KC_{rsp}M⁵C₁^{RG2}, as table row 128 and l.130 already did. Table row 128 is unchanged (0ec98b054ccd).
- **TB13-2 (MINOR): repaired.**
  - On Z, U's 𝐁_k″(Y₁)-data on Λ ∩ Ω″^{∼2}_{h+1} are averages at the scales h+1, …, k (LFR I (1.10)–(1.13), p.179, checked: Ω″_j on Z for j = k, …, h+1). The T-step's data are scale-k on Z (LFR II (1.33)).
  - So the first term changes by O(K)sup|B′|, by VAR Proposition 9 and (190). l.130 now says so.
  - l.167's K now also covers U_{k,Z}'s set 𝐁_k(Z) (LFR II p.367 l.11, checked).
  - The final constant is unchanged, since O(K)C₁^{RG2} ≤ KC_{rsp}M⁵C₁^{RG2}.
- Note SHA 7180a137c7ef → 56eb96e603fd; 948 lines.

**Next:** TB14 (`scope_twoloops_RevalTransferB14.md`). If TB14 is clean, it is TB's second clean round (TB8, TB14).

## (R-eval) Packet TB, Round TB14: Triage (3 November, 15:36–15:58)

Referee result: `referee_cli_20261103-153616_scope_twoloops_RevalTransferB14.json`. No ERROR, GAP, or OVERCLAIM.
- TB13-1 is repaired: every δ^{re} constant at the T-step's base (l.45's C_{mx}, l.130, l.160, l.161, and l.165) carries + KC_{rsp}M⁵C₁^{RG2} and matches table row 128.
- TB13-2 is repaired in substance. The O(K)sup|B′| step is right, K covers 𝐁_k(Z) (LFR I (1.74), p.192 l.52; CRE (2.13)) with a factor depending on d and L only, and the final constant absorbs O(K)C₁^{RG2}ε_k.
- **TB14-1 (MINOR, wording; repaired).** On the strip Λ ∩ (Ω″^{∼2}_{h+1}∖Ω″_{h+1}), U's data are at scale h, not h+1, …, k, since Γ″_h = (Ω″_h∖Ω″_{h+1})^{(h)} (LFR I p.179 l.44, checked; LFR II (1.52), p.370 l.19, checked). The step needs only j ≤ k, so no bound changes. The TB13-2 entry above made the same slip ("checked: Ω″_j on Z for j = k, …, h+1"). l.130 now reads "averages at scales j ≤ k, namely h on the part outside Ω″_{h+1}, … and h+1, …, k inside it".
- Under the clearance rule (a wording minor with no gap in the mathematics), TB14 is **clean**.
- Note SHA 56eb96e603fd → 7646f1732ca4; 948 lines.

**Packet TB is cleared** (clean rounds TB8 and TB14). **Next:** packet JB, R-eval-Jbase, written into l.173 and then reviewed. l.130 keeps its Open (R-eval-Jbase) label until JB has two clean rounds.

## (R-eval) Packet JB: Written Into l.173, Pre-Checks, Round JB1 Launched (3 November, 15:52–15:59)

- l.173 gains *The real base current*. It is the JB draft's derivation (WILSON_IT1_JBASE_DRAFT_2026_11_03.md, 14:35–14:42), with two changes found in the pre-check:
  - B_J is now the sup over the bonds with an endpoint in Ω_1, not over all layers. Off these bonds f = 1 (REG (1.70) at j = 0 is an empty sum), and at these bonds every plaquette lies in Ω = Ω_1^∼, so the restricted problem's current is J_k's. At bonds of ∂Ω the restricted current omits plaquettes off Ω, so the old "every bond of Ω" was wrong there.
  - U_k's membership in the restricted space at the bonds of ∂Ω is shown from the layer-0 bound: the current there is at most C(d)ε_0η^{−1} < B₃ε₁η^{−1}.
- Pins checked against the print: VAR (2) and (7) (p.278 l.3–7, l.34–45), Theorem 1 and its uniqueness clause (p.279 l.8–15), (28) (p.282 l.34); CMP98 Proposition 2 (p.26 l.46–53; units: its k := j, α₀ := (1+β₀)L²α_{0,k}); CRE p.246 l.4–6 and l.21–22, p.248 l.8–12, (1.11)–(1.12) (l.21, l.33), l.37, p.255 l.8–10, p.256 l.58–61, (2.34) (p.261); REG (1.70) (raw p.88 l.39–45); LFR I p.177 l.17–33; LFR II (1.33) (p.365 l.2–7); map l.313–316 (the real-U part of (2.34) is posed on every Ω_n∖Ω_{n+1}, n ≥ 1, and on Ω_k).
- l.130: B_J's definition is changed, the route paragraph is replaced by the pointer to l.173, and a remark covers the factor L at the layer boundaries. l.38, l.154, and l.213 name B_J. The Open (R-eval-Jbase) label stays, with "derived at l.173 and awaiting review".
- Note SHA 7646f1732ca4 → ba7c308bee79; 948 lines.
- JB1 launched at 15:59 (`scope_twoloops_RevalJbase1.md`).

## (R-eval) Packet JB, Round JB1: Triage (3 November, 16:14–16:20)

Referee result: `referee_cli_20261103-155903_scope_twoloops_RevalJbase1.json`. No ERROR. B_J ≤ B₃ε₁′ is correct where l.173 states it, and the layer-by-layer (7), the uniqueness clause, the current, f = 1 at layer 0, the persistence through R, and every pin check out. There are three MINORs, all real gaps, so JB1 is **not clean**.
- **JB1-1 (repaired).** l.130 (b) uses J_k at its real base U_{k+1}, which is not shown to lie on the support. l.173 now transfers the bound: some U^{B′} on the support is a D(k)(iii) base point and equals e^{iη𝐇(1,B′)}U_{k+1} up to a G-valued gauge (RG1 (2.6)). VAR Proposition 9 and (190) bound the current of 𝐇(1,B′) by O(K)sup|B′|, so B_J(U_{k+1}) ≤ B₃ε₁′ + O(KC₁^{RG2})ε_k → 0. l.130's pointer now states both bounds.
- **JB1-2 (repaired).** The collar χ_0 functions are dropped at step 1, not kept (CRE p.248 l.11–12, checked). l.173 now gives the support-projection argument: V_0 and V⌈Γ_1 are never integrated later, so the step-1 bounds involving only them hold on the step-k integrand's support. The wrong citation of p.255 l.8–10 is removed.
- **JB1-3 (repaired).** U_k's own support is a small neighbourhood of Ω_1 with a layer of M_1-cubes (CRE p.255 l.21–23, checked), smaller than Ω = Ω_1^∼. l.173 now covers the rest of Ω's layer-0 collar by the ε_0 bound, for both the plaquettes and the current.
- Note SHA ba7c308bee79 → a86970938b55; 948 lines.
- R-eval-old: work on the draft is stopped. Its input (note l.5) is the response bound at VAR's representative, which the fork's LF l.6 derives ((a) hole-filling Morrey bounds at Λ's faces, edges, and vertices; (b) the weighted bound (KW)). Note l.5 takes LF's bound once that is reviewed. The draft keeps the free-case joint gap and the d = 2 numerics: on a pinned stripe the joint gap decays slowly in L, from 0.911 at L = 3 to 0.712 at L = 10 (log-slope about −0.24), and with one pinned block from 0.839 to 0.544 (slope about −0.4); the weak mode is a ζ boundary layer on the pinned side.

**Next:** JB2 (`scope_twoloops_RevalJbase2.md`).

## Open (R-eval-old): Work During TB6 (3 November, 12:40–12:55)

- The peer's large-field note now takes C_H for the global Landau representative v = ∂₁*Δ^{−1}F, since the slice-gauge pointwise bound fails at Λ's re-entrant edges and corners.
- l.5 now names the input in REG's terms. C_{resp,∞} at i′ = 0 is the norm B₀ of H(U₀) (REG p.86 l.52–53), printed as depending "on d and L only" (p.87 l.16), and it is needed o(L) in data units.
- v's bound does not control the gradient part Dλ, λ = Δ^{−1}D*a, of VAR's representative, which satisfies only R(U₀)D*a = 0. The peer was told.
- CMP98 Proposition 10 ((207)–(214), p.50) was read. It linearises the averaging of gauge functions and gives no interpolation bound.
- **The P ≠ ∅ terms: closed (13:05–13:11, derived, awaiting review).** Components of (Ω″^∼_{h+1})^c ∩ Ω_h with P ≠ ∅ carry new large fields and are excluded from Z, and the new Z carries χ_{h,1/2} of the whole domain (LFR I p.198 l.2–4). Λ ⊂ Z ((1.73), p.192 l.43), so P = ∅ on Λ^{old}. There (1.91) (p.198) with (1.95) (p.199) bounds the curvature of U″_{k,Z} by (½ + 2α + O(αε_h))ε_h(L^{k−h}η)². The first draft wrote ½ + α from (1.91) alone; (1.95) adds the second α. l.5 now names a single input: B₀ = o(L).
- **B₀ = o(L) by L = L₀^m: doesn't work for the multi-layer domains.** B₀ is PBG Theorem 3.1/3.3's constant (CMP 99 p.397 l.37, "dependent on d and L only", uniform over sequences satisfying PRT II (2.1)–(2.2), PBG p.399 l.2). Q_{L₀}^m = Q_{L₀^m} makes one L-step equal to m L₀-steps on the full lattice. But PRT II (2.2) (p.224) separates Ω_j^c from Ω_{j+1} by only RML^jη, and equal consecutive domains are admitted only as T_η, so the m − 1 intermediate L₀-layers do not fit.
- **Where L enters B₀.** In PRT II the L-dependence enters through the local unit-lattice forms: Δ₀ + aQ₁′*Q₁′ ≥ γ₀′ with γ₀′ = π²/L² (p.242 l.42–43), which gives (2.110)'s γ₀, γ₁ "dependent on d and L only" (l.48), and through the decay rates δ₂, δ₃ of Propositions 2.5–2.6 (p.246 l.35, p.247 l.23). An o(L) bound must track these at the interfaces Λ_j | Λ_{j+1}, where L^j-blocks meet L^{j+1}-blocks.

## (R-eval) Packet JB, Round JB2: Triage (3 November, 16:41–16:47)

Result: referee_cli_20261103-162024_scope_twoloops_RevalJbase2.json (launched 16:20, landed 16:41). Not clean: one ERROR. JB1-1 to JB1-3 confirmed repaired; everything at D(k)(iii)'s pre-R base points confirmed (f = 1 on layer 0, persistence through R, VAR (7) at ε₁′ on every layer, the uniqueness clause, the current, ε₁′ → 0, l.130's arithmetic, the pins, the status sentences).

- **JB2-1 (ERROR), accepted and repaired.** "At part (b)'s base." called U^{B′} = U_k(e^{iB′}V) one of D(k)(iii)'s real base points. U^{B′} is the post-R background U_{𝐁_k}(V) (LFR II (1.35); l.132), and D(k)(iii)'s points are pre-R (l.174; l.175 does not derive the post-R clause). On Z the post-R data are new, and the pre-R derivation does not give VAR (7) there. Repair (l.173): the referee's first route, with the sources read.
  - LFR II Theorem 1 (p.355 l.17–21): the effective densities "have the form, and satisfy all the conditions and bounds, described in Sect. 2 [III]". Accepted.
  - The new regions, read off the print: LFR I (1.12)–(1.13) (p.179 l.32–47) give Ω_j″ = Ω_j ∩ Z^c off Z and Γ_0″ = Ω_1^c; LFR II (1.33) (p.365 l.2–7) gives Γ_j′ = Γ_j″ ∩ Z^c for j < k and Γ_k′ = Γ_k″ ∪ Z^{(k)}. So Ω_j′ = Ω_j ∪ Z for 1 ≤ j ≤ k and Γ_0′ = Ω_1^c ∖ Z.
  - The post-R base-point clause: map l.174's derivation from the printed small-field functions of a CRE Sect. 2 term, applied to the post-R term by D2.7 item 15.8 (derived, not reviewed; its O3 base points are "conditions on CRE's objects of the term and not on the step number"), as l.175 already records.
  - The derivation then runs at U^{B′} with Ω_1′, Ω′ = Ω_1′^∼, and the post-R support: Ω_1′^c is a union of whole components of Ω_1^c (Z is a union of whole components of Λ_k^c ⊇ Ω_1^c), so layers 0 and 1 and the margin carry over; on Z the data are in layer k ≥ 2, since R acts only at k > N (D2.7 item 13), and (7) comes from (2.34)-real by CMP98 Proposition 2 as for layers j ≥ 2.
  - l.130's pointer now says B_J at U_{k+1} is over the post-R Ω_1 = Ω_1 ∪ Z and names the post-R clause's source.
- Noted, not a finding: in l.173 and l.130, K denotes both VAR's factor O(C_dS_L) (fixed after d and L) and the final step; the bound O(KC₁^{RG2})ε_k → 0 is uniform in the step count either way.

Note → 2943e1e24c98 (948 lines). JB2 does not count; JB needs two clean rounds from JB3.

**Next:** JB3 (`scope_twoloops_RevalJbase3.md`).

## (R-eval) Packet JB, Round JB3: Triage (3 November, 17:01–17:03)

Result: referee_cli_20261103-164623_scope_twoloops_RevalJbase3.json (launched 16:46, landed 17:01). CLEAN: no ERROR, no MINOR. JB2-1's repair confirmed (post-R regions from LFR I (1.12)–(1.13) and LFR II (1.33); layers 0 and 1 and the margin carry over; Z in layer k ≥ 3 since N > N_0 ≥ 1; f = 1 off Ω_1′; the transfer with both B_J over Ω_1′; no circularity through D2.7 15.8, whose clause used is real-data only and whose OPEN O2 concerns the step-1 labels). Full pass at the pre-R points correct; all pins, the new ones included, match.

- Remark (not a finding), applied: l.18, l.173's bullet heading, and l.175 named only the pre-R clause as an input; each now also names D2.7 item 15.8's post-R clause for the transfer to U_{k+1}. Wording only, no change to the mathematics.

Note → 6a6770de2265 (948 lines). JB3 is JB's first clean round.

**Next:** JB4 (`scope_twoloops_RevalJbase4.md`), the second clean round needed.

## (R-eval) Packet JB, Round JB4: Triage (3 November, 17:13–17:16)

Result: referee_cli_20261103-170202_scope_twoloops_RevalJbase4.json (launched 17:02, landed 17:12). CLEAN: no ERROR, no MINOR. The three reworded input statements are accurate; the full pass (pre-R and post-R) is correct; all pins match. JB3 and JB4 are two consecutive clean rounds of the reviewed text.

- **Left unchecked in JB1–JB4: VAR's geometric conditions for the support Ω (and Ω′) with 𝐁_k's layering. Closed (17:13–17:15, derived, awaiting review).** VAR p.277 l.11–17: Ω_j unions of big blocks of size M_1L^jη, and (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM_1 with R ≥ R_1^V. Ω_1 is a union of LMR_1-cubes (CRE (1.10), p.248 l.7), ∼ adds one layer of the defining cubes (p.245 l.40–43), the partitions are compatible (p.245 l.38–40), so η^{−1}dist(Ω^c, Ω_1) ≥ LMR_1, and CRE's R_1 ≥ (log g_1^{−2})^r (CRE (2.5), p.255 l.36–39) exceeds R_1^VM_1/(LM) for g small. For j ≥ 1 the sequence is 𝐁_k's own (unchanged by the restriction). Post-R: Ω′∖Ω_1′ is the layer along the remaining parts of ∂Ω_1, and for j ≥ 1 the post-R sequence is the one of LFR II (1.35). Written into l.173 (after "the same conditions (2) off Ω." and in the post-R inputs).

Note → db43afc719f9 (948 lines). The new sentences are new content: Open (R-eval-Jbase) stays until they have two clean rounds (JB5, JB6), scoped to them and to their use in the passage.

**Next:** JB5 (`scope_twoloops_RevalJbase5.md`).

User (17:2x): a minor addition needs only one round.

## (R-eval) Packet JB, Round JB5: Triage (3 November, 17:25–17:27). Packet JB CLEARED

Result: referee_cli_20261103-171511_scope_twoloops_RevalJbase5.json (launched 17:15, landed 17:24). No ERROR; one MINOR of attribution kind, so clean under the clearance rule. The two new sentences on VAR's geometric conditions are correct before and after R, (1) at j = 0 uniformly in k; the full pass unchanged and correct.

- **JB5-1 (MINOR, pin), repaired:** "CRE (1.10), p.248 l.7" → "p.248 l.8" (l.7 is the \end{equation}; "thus Ω_1 is a union of LMR_1-cubes" is l.8).
- **Packet JB cleared** (JB3, JB4 clean on the passage; JB5 clean on the minor addition). Open (R-eval-Jbase) removed: l.7 (R-eval's status: reviewed for the real base current), l.8, l.38, l.130 (three places), l.154, l.159, l.173's heading ("derived and reviewed as packet JB; the transfer to U_{k+1} given D2.7 item 15.8"), l.213, l.785. B_J at U_{k+1} rests on D2.7 item 15.8's post-R base-point clause (derived, not reviewed).
- JB5's "not checked": Bałaban's own claim that 𝐁_k's sequence, before and after R, satisfies VAR (1) for j ≥ 1 (taken from his use of VAR, accepted).

Note → db6d1358cb87 (948 lines).

## R-eval Status Check (3 November, 17:33)

User asked whether the R-eval opens are at least provisionally closed. Neither is: l.5 (R-eval-old) reduces to C_{resp,∞} = o(L) from LF l.6, which is derived, not reviewed, and NOT ESTABLISHED after r38 (four serious findings accepted, repairs in progress); l.6 (R-eval-curv) reduces to the margin at 𝕌^{(0)}, derived nowhere (LF l.6's open (b) is shared with it). The R-eval packets A, B, C1, C2b are reviewed next with both opens declared "open, not findings", as JB was, after (R-round) 2a.

## (R-round) Round 2a: Triage (3 November, 17:41–17:47)

Result: referee_cli_20261103-172730_scope_twoloops_Rround2a.json (17:27–17:41). One ERROR, one MINOR. Everything else in l.234–239 and l.690–721 checked, including all arithmetic.

- **TL-Ra-1 (ERROR), accepted and repaired.** l.699 said the 𝒦 ≠ ∅ part of a carried insertion outside every X⁺ is not a member of 𝔅(P) and enters only by its tree's ℓ_a/M + 3. But D2.7 15.5(i) joins its domain to the polymers of 𝒦 (15.5(ii): "the attached insertions are slots of the polymers of 15.3"), and l.617 puts its intervals in ℐ(g); so σ_g, σ̄(g), *Cubes*, *Traversals*, and *Diameter* missed it, and a large attached dev insertion broke the 6σ_g units. Also l.699's "paid through its mass in the sum a_k(X)" misread a_k(X), a sum over the attachment bonds (D2.7 15.5(ii)). Repair, the referee's first route:
  - l.699: 𝔅(P) now holds the arc-slot members and the attached carried insertions. Big attached members are counted by (21/20)σ(D) and paid from their weights, as every big member.
  - A small attached member (j < k, #_k < 22, n_k < 22.5M, diam T_D ≤ 21M) lies at ℓ^∞-distance ≥ 2MR_k − 21M ≥ MR_k from 𝒦's components (its interval is outside every X⁺, which adds two layers of MR_k-cubes), so ℓ_{a′} ≥ MR_k and ½ℓ_{a′}/M ≥ 23 for R_k ≥ 46. D_P (l.627) now gives each attached carried insertion (3/2)ℓ_{a′}/M; the half length covers its 22 cubes, its < 22.5M ≤ 16M·½ℓ_{a′}/M interval bonds, and 23M of diameter.
  - Payment: 15.5's sums now run at δ/4 (l.613: a_k(X) ≤ 16(100MR_k + 2Mw_k + 8Mδ^{−1})δ^{−1}e^{−δw_k/4}, D2.7's sum at δ/4; the old l.613 formula also dropped D2.7's 2Mw_k and M factors), leaving e^{−(3δ/4)ℓ}: c_F per unit of (3/2)ℓ_{a′}/M needs (3/2)c_F ≤ 3δM/4, which c_F = min(1, δM/2) satisfies (l.638). l.646 now concerns the attached bond insertions only.
  - Propagated: l.626–627 (a and a′), l.629, l.631, l.698 (arc-slot case), l.711, l.714 (*Cubes*), l.715 (*Traversals*), l.720 (*Diameter*); R_k ≥ 46 added to the conditions list (l.286).
- **TL-Ra-2 (MINOR), repaired.** l.693: u_D ≤ 19; l.700 now lists D_G (u = 19) and its untouched continuations.
- **Outside the scope, repaired:** l.570's stale phrases: u ≤ 21/10 (not 21/20) for single-loop R-made insertions without a carried slot insertion, and "untouched continuations" for the R-made cross insertions.

Note → de0f1f3b546b (948 lines). (R-round) part a needs its next round: `scope_twoloops_Rround3a.md`.

## R-eval Scopes Refreshed; l.5's C_H Status Updated (3 November, 17:48–17:52)

- **Scopes ready, each with Open (R-eval-old) and Open (R-eval-curv) declared, not findings:** `scope_twoloops_RevalA7.md` (A6-1 to A6-5, admissibility, Ω_{k+1} ⊂ Ω_j across R-steps), `scope_twoloops_RevalB2.md` (B1-1 to B1-4, the region near Λ inside X^∼, (1.65) per component), `scope_twoloops_RevalC12.md` (C1-1.1 to C1-1.6, PRT2 (2.46)), and `scope_twoloops_RevalC2b8.md` (C2b7-1; Open (R-eval-transfer) dropped, closed as packet TB). Ranges checked against the note: A l.38–76, B l.77–89, C1 l.90–121, C2b l.140–166. `scope_twoloops_Rround2b.md` now lists part a's changes (attached carried insertions as members, D_P's (3/2)ℓ_{a′}/M, u_D = 19) and the current context ranges. `scope_twoloops_Rattext2.md` ranges are current.
- **l.5, C_H's status.** The peer reported (17:50) that LF l.6's C_H is still not established and has a new open item, S5 (LF r38 triage l.46): the interfaces Λ_j/Λ_{j+1}, j ≥ 1, apart from the part of Λ₁ at distance ≥ CL(1 + log L)³ from Λ₂. l.5's stale description (the blocks of Λ′ next to Λ^c, the re-entrant corners, the layer term of T) was replaced by S5, checked against the triage file. Open (R-eval-old) itself is unchanged. Note → a5a5d5fb1dec (948 lines, LF line endings as before). l.5 is outside R-round 3a's scope.

## (R-round) Round 3a: Triage (3 November, 18:03–18:15)

Referee run `referee_cli_20261103-174633_scope_twoloops_Rround3a.json` (17:46–18:03): one ERROR and three MINORs. Confirmed: the constants of *The units of the members* (16.1 + 0.23σ, 17 + σ/4, the L₀^× checks), the threshold 22, the attached members' ℓ_{a′} ≥ MR_k and ½ℓ_{a′}/M ≥ 23, l.613's a_k(X) as D2.7's formula at δ/4, (3/2)c_F ≤ 3δM/4, (105R_k)^d, the cross group's 6σ_g and 48.5 ≤ 64, (H0)–(H2), TL-Ra-2, and l.570. Every finding was checked against D2.7 15.5(i)–(ii) and 15.6(b) and accepted. The note was edited in place, with no line shift.

- **TL-Rb-1 (ERROR), repaired.** D2.7 15.5(i) also expands the slot insertions and the attached species in their U-argument ("they take the same expansion in their U-argument"). So their parts D^{𝒦}, 𝒦 ≠ ∅, have trees, which TL-Ra-1's split (a: bond insertions; a′: members outside every X⁺) left uncounted.
  - Now a′ ranges over all the parts D^{𝒦}, 𝒦 ≠ ∅, of the carried insertions in P's slots, with ℓ_{a′} := ℓ(X_D,𝒦) ≥ MR_k, each with the term (3/2)ℓ_{a′}/M (l.626).
  - A part with ℓ(X_D,𝒦) < MR_k has no term: its tree meets a component X″ ∈ 𝒦 of P and lies within MR_k of it, so inside X″⁺ ⊆ B_P and inside X″'s piece of *Lengths*.
  - The tree's cubes: (2^{d+1} + ½)(3/2)ℓ/M ≥ 2^{d+1}(ℓ/M + 1) for ℓ/M ≥ 2, and ℓ/M ≥ R_k. The free decay is (3/2)c_F ≤ 3δM/4, as before.
- **TL-Rb-2 (MINOR, unstated input), repaired by a clause of R-far″.** (α′): |D^{𝒦}| ≤ ‖D‖O(1)^{|𝒦|}e^{−δℓ(X_D,𝒦)}, with ℓ(X_D,𝒦) the scaled length of the shortest tree connecting X_D and the components of 𝒦, and ‖D‖ D's bound at the U^{𝒥} (l.619).
  - Bałaban's factor exp(−δd((Y₁⁰)^c ∩ Y₁ ∩ Y_i′, X)) (LFR II p.376 l.10–13) is the decay of a term localised in a domain X in the scaled distance from X. So (α′) is the printed factor's own form, and (α) is its case of one bond.
  - Stated in the note's *15.5* (l.613), used at l.638 and l.744, and added to D2.7 15.5(ii) after (α), since D2.7's single-loop slot insertions use the same parts. D2.7 → 992a70269a1f (was d091fb29cf09).
  - Checked and not sufficient: deriving (α′) from (α) by a Taylor expansion in the bond variables. Near the components |Y_b^{𝒦}| is O(1), not small against D's analyticity room.
- **TL-Rb-3 (MINOR), repaired.** l.699 now lists the whole-joined att(j, Z′) and lw slots of a first-class Z′ (D2.7 15.5(i): "the whole insertion is then a slot inside Z′'s activity"). One dichotomy now covers every small member.
  - If T_D meets X⁺ for a component X of P, then T_D ⊆ X^{(22)} ⊆ B_P. Every arc-slot member is in this case.
  - Otherwise T_D is at distance ≥ 2MR_k from every component of P. Then (a) a part D^{𝒦}, 𝒦 ≠ ∅, joins it by a tree with ℓ_{a′} ≥ 2MR_k, whose half term ½ℓ_{a′}/M ≥ 46 covers 22 cubes, 22.5M bonds, and 23M of diameter; or (b) for a whole-joined member's 𝒦 = ∅ part, each piece's connected Y′ ⊇ X_D ∪ Z′ (15.5(ii)(β)) has #π_k(Y′∖Y′₀) ≥ 2R_k − 1 ≥ 91. One half of D_P's term 2#π_k(Y′∖Y′₀) is the piece's own, and the other covers the same count.
  - Propagated: l.629, l.711, l.714 (*Cubes*), l.715 (*Traversals*), l.720 (*Diameter*), l.761 (*First case*).
- **TL-Rb-4 (MINOR), repaired.**
  - l.238 now states the dichotomy.
  - l.523: a small W's T_W lies in X^{(22)} or is covered by half of its tree's or piece's term, so at most Σ_P(#π_k(B_P) + D_P) ≤ σ_g cubes.
  - l.521, l.522, l.524: an attached big cross member made at step k gets a second segment, from X_W to its interval in its slot, at ≤ 18.4σ(W) for both segments. A member made at j < k is joined by T_W = X_W ⊇ ℐ(W).
  - l.571: 18.4Σσ(W) + Σ_P(#π_k(B_P) + D_P) ≤ 19.4σ_g ≤ 29σ_g, so 419σ_g + 160 is unchanged.
  - (R-member) l.257: segments and small T_W ≤ 19.4σ(D_G), in all ≤ 1705σ(D_G) + 160 (19 + 1216 + 19.4 + 450 = 1704.4), domain 218240σ(D_G)/L (1705·128), share (221584·17/16 + 209)/10⁶ = 0.2356 ≤ 0.236; l.572 and l.696 (218240/L₀^× ≤ 0.22) follow.

Note → fd81bd1df34a (948 lines). (R-round) part a needs its next round: `scope_twoloops_Rround4a.md`.

## (R-round) Round 4a: Triage (3 November, 18:34–18:55)

Round 4a ran 18:16–18:34 (`referee_cli_20261103-181622_scope_twoloops_Rround4a.json`). It found one ERROR and one MINOR. TL-Rb-1, TL-Rb-3, and TL-Rb-4 are confirmed repaired, and TL-Rb-2's (α′) is confirmed as a correctly quoted named reading.

- **TL-Rc-1 (ERROR), repaired.** The finding was correct. (α′) puts C_α^{|𝒦|} on each part, and the members per bond are not bounded uniformly in k (l.235; D2.6 5.2 (T0) *Positions*). So "as the bond insertions' do" left a per-member factor unpaid, which is O(1) for the near parts. The referee's failure case was N members within 2MR_k of a component, giving Π(1 + c·e^{−δMR_k/2}).
  - **Home rule** (l.613; D2.7 15.5(i), (α′)).
    - A carried insertion is expanded about its home h(D): the first-class components whose X⁺ meets X_D, plus Z′ for an att/lw insertion of a first-class Z′.
    - The components of h(D) keep their old data in every configuration, as h(i) does for a bond. This is the exact Möbius identity with base U^{h(D)}.
    - D^{∅} is joined to h(D)'s polymers (D is untouched if h(D) = ∅), and D^{𝒦} to those of h(D) and 𝒦.
    - No near parts remain: every X ∈ 𝒦 has X⁺ ∩ X_D = ∅, so ℓ(X_D,𝒦) ≥ MR_k. *Lengths* l.626 now says every part has ℓ_{a′} ≥ MR_k, and l.761's parenthesis on short trees is removed.
    - l.699's "attached" kind is restated through h(D). A small member joined through its home has T_D meeting X⁺, so it is in the dichotomy's first case.
  - **Far-part bound** (l.613). η(D) := Σ_{𝒦≠∅}C_α^{|𝒦|}e^{−(δ/4)ℓ(X_D,𝒦)} ≤ 3^d#_k(X_D)e^{−δMR_k/8}.
    - The MR_k-cubes meeting the shortest tree form a ∗-connected S with m ≤ 2^{d+2}ℓ/(MR_k) cubes.
    - Components are unions of MR_k-cubes (LFR I p.177 l.17–19), so each X ∈ 𝒦 owns a cube of S. That gives (1 + C_α)^m per S.
    - Lattice animals contribute (e3^d)^m, and a root cube meeting X_D gives ≤ 3^d#_k(X_D). A closed cube can touch X_D only on its boundary; that is the reason for the 3^d, caught in the self-check.
    - The rate is split: e^{−(δ/8)ℓ} ≤ e^{−δMR_km/2^{d+5}} and e^{−(δ/8)ℓ} ≤ e^{−δMR_k/8}. With x := e3^d(1 + C_α)e^{−δMR_k/2^{d+5}} ≤ ½, the sum is at most that bound.
  - **Payment** (l.722, l.731, l.732, l.742, l.744, l.772, (H^R) l.774–776, (6C) l.844, conditions l.286).
    - The rate becomes λ_n := 1 − Σ(ε_k + ϑ_k), with ϑ_k := e^{−δMR_k/16}. Then η(D) ≤ 18.05·3^dσ(D)e^{−δMR_k/8} ≤ (ϑ_k/4)ν_rσ(D), under 73·3^de^{−δMR_k/16} ≤ ν_r.
    - Each member carries e^{−((ε_k+ϑ_k)/4)ν_rσ(D)} in the rooted sum. A cross member enters at w_{k−1}e^{−(ε_k/2+ϑ_k)ν_rσ}, so l.769's w_{k−1}e^{−(ε_k/4)ν_rσ} stands.
    - The single-loop member's total is ≤ e^{(1/2 + 3ε_k/4 + ϑ_k/4 + 1/4)ν_rσ}.
    - For h(W′) = ∅, the untouched part and the member parts together are ≤ (1 + η)e^{−ϑ_kν_rσ}w_{k−1} ≤ w_{k−1}.
    - In (6C) the reserve pays the factor since ½ + 1/10 + ϑ_k/4 ≤ 1.
    - (H^R)'s S^R gains Σϑ_k. R_k ≥ (log u_k)^r with r ≥ 2 (CRE p.245 l.32–33, p.246 l.24–25), so ϑ_k ≤ u_k^{−2} once δM log u ≥ 32, and S^R ≤ 2u^{−2} + 2(bu)^{−1}.
- **TL-Rc-2 (MINOR), repaired.** l.572 now reads C_win ≤ 196·19/c_w, "factors up to 19, the merged insertions of (R-member) included". The condition for u ≤ 16 is (2720 + 59584/c_w), implied by l.258's (3230 + 70756/c_w).

Note → c4de832ceaaf (948 lines). D2.7 → 75c83d56c50c (15.5(i) home rule, (α′) with base U^{𝒥∪h(D)}); peer notified. (R-round) part a needs its next round: `scope_twoloops_Rround5a.md`.

## (R-round) Round 5a: Triage (3 November, 19:11–19:20)

Round 5a ran 18:51–19:11 (`referee_cli_20261103-185120_scope_twoloops_Rround5a.json`). It found two ERRORs and two MINORs. Confirmed correct: the Möbius identity about U^{h(D)}; the η proof (cube count, (1 + C_α)^m, animals, roots, rate split, x ≤ ½); the exponents at l.731, l.732, l.742, l.769, and l.772; (6C)'s ½ + 1/10 + ϑ_k/4; (H^R); the dichotomy; and TL-Rc-2.

- **TL-Rd-1 (ERROR), repaired.** The home used the counted domain X_D. A step-k insertion depends on U^{old} on its Cov domain, which contains ℐ(D) (l.508; map l.622) and need not lie in X_D. So an interval crossing C ∩ X⁺ with X_D missing X⁺ left a near part of order ‖D‖.
  - The home is now defined from the dependence set Dep(D) := X_D ∪ X^{Cov}_D (⊆ T_D; = X_D for j < k): l.613, l.699, D2.7 15.5(i) and (α′). l.613 states that an interval meeting C ∩ X⁺ forces X ∈ h(D).
  - ℓ(X_D,𝒦) is renamed ℓ(D,𝒦), the tree from Dep(D) (l.613, l.626, l.744; D2.7 l.175). *Lengths* l.629 now builds dom P from the sets T_D ⊇ Dep(D), so the trees ending on Dep(D) keep it connected, with diam_∞(T_D) ≤ M(21/20)σ(D) for big members (l.698).
  - The root count is now over the cubes meeting Dep(D). By (H0), Dep(D) ⊆ N_{8M}(X_D ∪ ℐ(D)) and 8M ≤ MR_k, which gives ≤ 3^d(3^d#_k(X_D) + 2^dn_k(D)) ≤ c_rσ(D), with c_r := 18.05·3^d(3^d + 2^dM) (l.694). So η(D) ≤ c_rσ(D)e^{−δMR_k/8}. *The rates* l.722 and l.286 now use 4c_re^{−δMR_k/16} ≤ ν_r.
- **TL-Rd-2 (ERROR), repaired.** Single-loop weights have no decrement. A single-loop insertion with h(D) = ∅ is untouched on D^{∅} at full weight and a member on its other parts.
  - (6C) *The members' weights* (l.844) now books this. The member parts use ≤ 0.89 of the reserve besides η (l.732, l.844, l.858). So the options together are ≤ e^{ν_rσ}‖D‖(1 + ηe^{−0.11ν_rσ}) ≤ (1 + y^s_k)e^{ν_rσ}‖D‖, with y^s_k := C_se^{−δMR_k/8} and C_s := 10c_r/(eν_r).
  - D2.6 5.3: M_k ≤ (1 + δ_{k−1} + y^s_k)M_{k−1}, under C_δc̄S_R + C_sS^R ≤ log 2.
  - Map l.1377's dev recursion: the carried terms gain the factor ≤ 33/32. It stays uniformly bounded, since (33/32)·1.5⁸ < 5000.
  - Conditions added at l.286. D2.7 15.5(i) now names the three payments: cross through ϑ_k, single-loop member through its reserve, and single-loop untouched with an empty home through the growth 1 + y^s_k.
- **TL-Rd-3 (MINOR), repaired.**
  - l.264 now reads = w_{k−1}e^{−(ε_k+ϑ_k)ν_rσ}, with ϑ_k/4 paying 1 + η(W) and at least ε_k/4 left.
  - l.858 books ϑ_k/4. The total is still ≤ 0.89: 0.8583 + 3/128 + 1/128 = 0.8896.
- **TL-Rd-4 (MINOR), repaired.**
  - l.619 now evaluates the parts at U^{𝒥∪h(W)}.
  - l.780 defines "untouched" as h(W) = ∅, so Dep(W) ⊇ ℐ(W) meets no X⁺, and the term takes W^{∅} = W(U^R).

Note → 808b9f1deafb (948 lines). D2.7 → a3a559b7f16b; peer notified. (R-round) part a needs its next round: `scope_twoloops_Rround6a.md`.

## (R-round) Round 6a: Triage (3 November, 19:33–19:40)

Round 6a ran 19:18–19:33 (`referee_cli_20261103-191853_scope_twoloops_Rround6a.json`). It found one ERROR and four MINORs. Confirmed correct: the home via Dep(D) (it agrees with the arc-slot rule and l.780); the η bound and c_r; the payment exponents; l.858's 0.8896; y^s_k and the dev recursion; (H^R); the count and rounding; and the pins.

- **TL-Re-1 (ERROR), repaired.** Putting T_D into dom P (l.629) put the cubes of a step-k member's Cov domain and interval into hull(g), and so into X_{D_g^×} and X_{D_g}. The cube counts (l.714, l.716, l.721, l.706–710) count only X_D. l.617's Y′₀ ⊇ X_D also needed Dep(D).
  - **l.617.** Y′₀ ⊇ Dep(D), and R-far″ claims no decay across Dep(D). Dep(D) ∖ X_D lies within 8M fine units of X_D ∪ ℐ(D) by (H0) (l.509), which is less than one π_k-side. It is left out of the counted domains, and the intervals are counted as traversals.
  - **l.629.** dom P is built from the sets Dep(D), which keeps it connected. Its counted domain dom_c P is the set of the π_k-cubes meeting dom P ∖ ∪(Dep(D) ∖ X_D). Each component of the remainder comes within less than a π_k-side of X_D ∪ ℐ(D), so its cubes touch E_D of (H2). For the diameter, Dep(D) ⊆ T_D.
  - **l.678.** hull(g) is kept for the dependence. The counted domain is hull_c(g) := ∪dom_c P, and #π_k(hull g) denotes its cubes. The members' intervals lie in Dep(D), not in hull_c(g); they are counted as traversals.
  - **l.706 and l.707.** X_{D_g} now uses dom_c P. (H2) holds because the remainder's components touch E_D, whose intervals lie in the slot, so in span(g).
  - **l.714.** Y′₀'s counted cubes are in B_P, on the trees, or in the big members' X_D.
  - **l.721.** X_{D_g^×} := hull_c(g). (H0) holds because the excluded points and the members' Cov domains are within 8M fine units of X ∪ ℐ(g). (H2) holds by the touching argument, since ℐ(D) ⊆ ℐ(g).
  - The units (6σ_g), u = 16, and σ̄(g) stand as before, since no uncounted cube enters.
- **TL-Re-2 (MINOR), repaired.** l.799's attached cross groups now book ϑ_k/4: 1/2 + 3ε_k/4 + ϑ_k/4 + 1/4 + 9/64 ≤ 0.922. In l.844 the fraction is now 0.922, the factor ηe^{−0.078ν_rσ}, and C_s := 13c_r/(eν_r) (1/0.078 ≤ 12.83).
- **TL-Re-3 (MINOR), repaired.** l.844 now reads M_k ≤ (1 + δ_{k−1})(1 + y^s_k)M_{k−1}, since the T-step and the R-step act in turn.
- **TL-Re-4 (MINOR), repaired.** D2.7 15.5(i) now covers every carried insertion, dev and cross included. (α′) now reads "a carried insertion D of (i), of any species".
- **TL-Re-5 (MINOR), repaired.** l.859 now reads (2720 + 59584/c_w), with C_win ≤ 196·19/c_w, implied by the u = 19 condition.

Note → 5cccff6d2e4f (948 lines). D2.7 → 8b55629b83a1; peer notified. (R-round) part a needs its next round: `scope_twoloops_Rround7a.md`.

## l.5: C_H Status Updated (3 November, 19:44)

The peer wrote S5 as LF (K0)(g), l.1009; LF is now 36e3acd5b3bb. LF l.6 now reads: "At the interfaces Λ_j/Λ_{j+1} with j ≥ 1 the same holds in the units of L^j (l.1009 (K0)(g)), and the norm of the chain is ‖·‖_{W_ms}". l.5 now states that C_H ≤ C(d)(1 + log L)^p is derived, not reviewed (LF l.6 and (K0)), with S5 as (K0)(g). The rest of (R-eval-old) is unchanged: the gradient part Dλ of VAR's representative and B₀ = o(L). l.5 is outside round 7a's scope. Note → cfab452e50b6.

## (R-round) Round 7a: Triage (3 November, 19:53–20:15)

Round 7a ran 19:40–19:53 (`referee_cli_*_scope_twoloops_Rround7a.json`). It found one ERROR and two MINORs. Confirmed correct: TL-Re-2 to TL-Re-5; the connectivity of dom P; (H0) and (H2) for D_g^× and D_g apart from TL-Rf-1; η(D) and c_r; the payments and (H^R); the units, the rounding, *Traversals*, and the arithmetic of *Together* and *Diameter* apart from TL-Rf-1; and the pins.

- **TL-Rf-1 (ERROR), repaired.** Y′₀ ⊇ Dep(D) is a union of π_k-cubes. For a member made at the T-step into step k it holds the cubes over ℐ(D) ∖ X_D. Removing points removed no cube, so dom_c P, hull_c(g), X_{D_g^×}, and X_{D_g} still held these cubes, uncounted. Their diameter also reaches up to M beyond T_D. The cubes are real: D_g^× depends on U^R on them.
  - **The cubes.** Q(D) := the π_k-cubes meeting Dep(D) ∖ X_D (l.693). Q(D) = ∅ when j < k. When j = k, D is T-made with u_D = 1, since R acts only at k > N_B and N_B > N₀ ≥ 1 (D2.7 item 1(b); LFR I p.179 l.8–10: N₀ is "the smallest positive integer" with L^{−N₀+1}MR_{k−N₀+1} = M, and "We assume that N > N₀"). So X^{Cov}_D ⊆ S_D = X_D ∪ ℐ(D) (l.517), Dep(D) ∖ X_D ⊆ ℐ(D), and every cube of Q(D) meets ℐ(D). In both cases Dep(D) ⊆ X_D ∪ ℐ(D).
  - **The count.** dom_c P is the set of π_k-cubes meeting dom P other than the cubes of the Q(D) (l.629). Every excluded cube meets ℐ(g), whose bonds are counted as traversals. The excluded cubes enter E_D, and through it the domain one step later, as cubes meeting H₁ ∪ H₂ ⊇ ℐ. (H0) now reads: X^{Cov}_D lies in the 8M-neighbourhood of X_D ∪ (the π_k-cubes meeting ℐ(D)) (l.509). Its only use, the domain one step later (l.512), holds because E_D contains those cubes. Every insertion has it: T-made (Cov ⊆ S_𝒢), step 1 (S_W), D_g^× (l.519), D_g (l.708), and D_G (through its groups). This also settles TL-Rf-2: l.518, l.519, l.521, l.523, and l.524 now use hull_c(g), and E_{D_g^×} contains every cube meeting hull(g).
  - **The diameter.** For j = k, T_D := S_D ∪ Q(D), with diam_∞(T_D) ≤ diam_∞(S_D) + 2M ≤ M(σ(D) + 2) (l.695). Big now means σ(D) ≥ 40 when j = k, and σ(D) ≥ 22 when j < k (l.698). A big step-k member keeps (21/20)σ(D), since σ + 2 ≤ (21/20)σ for σ ≥ 40. A small member, of either kind, has fewer than 40 cubes in X_D, fewer than 40M interval bonds, and diam_∞(T_D) < 42M.
  - **The widening.** X^{(22)} becomes X^{(44)}: 44 layers of π_k-cubes, which contain every small T_D that meets X⁺. Then 4R_k + 48 becomes 4R_k + 92 (l.633: 4R_k + 4 + 88). #π_k(X^{(44)}) ≤ (104R_k + 88)^d ≤ (105R_k)^d for R_k ≥ 88 (l.654; conditions list l.286). The margin's 5p₀/64 is unchanged.
  - **The joins (l.699 (a), (b)).** 40 cubes, 40M bonds, and a lengthening of 43M. These are covered by ½ℓ_{a′}/M ≥ R_k ≥ 46 and #π_k(Y′∖Y′₀) ≥ 91. The base in (b) is now the cubes of X_D, Q(D), and Z′.
  - **Uses.** These lines now use the new definitions: l.237 and l.238; l.613 (Dep(D) ⊆ X_D ∪ ℐ(D) in place of (H0), with c_r unchanged as an upper bound); l.617; l.678; l.703; l.707; l.714 (with #π_k(hull g) ≤ #π_k(hull_c g) + 2^d|ℐ(g)|); l.715; l.716; l.718 to l.721; and l.724 (with 2^{d+1} + ½ + 17·16M + 4M ≤ (1 + 20M)2^{d+2}).
  - **l.730.** The member part of |Ψ_g| is now ≤ 23C_Ψ′M·e^{−p₀/2}Σσ, since 17·21/20 + 4.2 ≤ 23. The condition 182C_Ψ′Mε_k ≤ ν_r still implies it.
  - Unchanged: u = 6, 16, and 19; σ̄(g); δ_P and the spans; *First case*'s 9; L₀^×; and (T0)'s constants.
- **TL-Rf-2 (MINOR), repaired.** l.518 to l.521 now read hull_c(g) (see above).
- **TL-Rf-3 (MINOR), repaired.** D2.7 15.5(i)'s parenthetical now gives two bounds. A single-loop species is bounded by its D(k) mass inside e^{2ΣA}. A cross insertion is bounded by its own weight, as a fixed factor of the words outside e^{2ΣA} (note (6B), *15.5*, l.618).

Note → f1a62d423299 (948 lines). D2.7 → 52921b7909c8; peer notified. (R-round) part a needs its next round: `scope_twoloops_Rround8a.md`.

## (R-round) Round 8a: Triage (3 November, 20:29–20:31)

Round 8a ran 20:16–20:29 (`referee_cli_20261103-201556_scope_twoloops_Rround8a.json`). It found no ERROR and four MINORs. TL-Rf-1 to TL-Rf-3 are confirmed repaired:
- Q(D) is empty for j < k.
- The j = k members are T-made with u_D = 1 (LFR I p.179 l.8–10 checked).
- diam_∞(T_D) ≤ M(σ + 2).
- The new (H0) holds for every insertion, and its only use is l.512.
- The 40/22 split, X^{(44)}, the joins, (105R_k)^d, and the |Ψ_g| constants all hold.

TL-Rg-1 is a real gap under one reading, so the round is not clean.

- **TL-Rg-1 (MINOR, a gap under the closed-cube reading), repaired.** "The π_k-cubes meeting a set" had no fixed convention. With closed continuum cubes, dom_c P would take in every neighbour cube of X′_r, Y′, and the big members' X_D. *Cubes* does not count those (the referee's example is a straight bar of n cubes, with about 27n neighbours). l.628 (*Lengths*) now fixes the convention for (6A) and (6B):
  - a π_k-cube is a block of the partition π_k of the sites;
  - it meets a set when it contains one of the set's sites (for a bond, an end site);
  - so the cubes meeting a union of cubes are its own cubes, a bond meets at most two cubes, and a lattice path of at most M steps meets at most 2^d;
  - diameters and closed-connectedness are taken on the closed hulls;
  - the MR_k-cubes of *15.5* stay closed continuum cubes, named as such.

  The referee confirmed that l.613–721 hold as written under this reading. The existing statements "a bond meets at most 2^d π_k-cubes" stay true as upper bounds.
- **TL-Rg-2 (MINOR), repaired.** l.645 now reads e^{c_F(4R_k+92)}.
- **TL-Rg-3 (MINOR), repaired.** l.855 now has 88M per localisation domain, e^{44n/R_k}, and R_k² ≥ 880/ν_r: 44n/R_k ≤ 11Σ_PD_P/R_k² by n ≤ Σ_PD_P/(4R_k + 92). l.856 now has 352M, e^{88n/R_k}, and R_k² ≥ 1760/ν_r. Both are still smallness conditions on g_k; the conditions list does not name them.
- **TL-Rg-4 (MINOR), repaired.** l.277 and l.837 now read diam_∞(T_W) < 42M for a small member, and e_W := 43, since Y_W lies within 42M + M of ℐ(W). l.843 now reads (3/4)ν_e·43 ≤ 4.1ν_r per group, using ν_e ≤ 0.127ν_r from the big-member line. It is still paid by the margin.
- **Queued repairs from the 7a self-check, applied.**
  - l.255 states D_G's (H0) in the new form: the groups' and the cross insertions' (H0), with their counted domains in X_{D_G} and their arcs in ℐ(D_G).
  - l.257 counts the small T_W's cubes outside the arc cubes.

Note → 61133a20467a (948 lines). D2.7 unchanged (52921b7909c8). (R-round) part a needs its next round: `scope_twoloops_Rround9a.md`.

## (R-round) Round 9a: Triage (3 November, 20:54–20:59)

Round 9a ran 20:32–20:54 (`referee_cli_20261103-203252_scope_twoloops_Rround9a.json`). It found no ERROR and three MINORs. It confirmed:
- TL-Rg-1 to TL-Rg-4. The l.628 convention works, since L is odd (RG I p.251 l.14).
- The repairs at l.255 and l.257.
- (H0)–(H2), Q(D), and T_D for every insertion, the wrap(j) insertions with h(D) = ∅ included.
- All the pins.

TL-Rh-1 and TL-Rh-2 are real gaps, so the round is not clean.

- **TL-Rh-1 (MINOR, a gap), repaired.** The straight segments in E_{D_g^×} fell outside the l.628 convention:
  - read by sites, a segment can leave an isolated cube;
  - read by closed cubes, a segment through a grid corner meets 16 > 9 cubes.

  They are not needed. A member W lies in a slot of a polymer P, and dom P contains Dep(W) ⊇ X_W ∪ ℐ(W) (l.508, l.629). So the cubes meeting dom P already join X_W to all of W's intervals.
  - l.521–524 now define E_D := hull_c(g) ∪ (the arc cubes), the plain (H2) form, with two sub-bullets: the members' X_W and intervals lie in dom P, and T_W ⊆ X_W ∪ (the cubes meeting ℐ(W)) ⊆ E_D.
  - l.511 drops "with the segment cubes below".
  - l.571 is now *Units with a factor* at u = 6: 390σ_g + 160 cubes, 49920σ_g/L, and 6(8496ν_f + 88ν_e)/L ≤ ν_r/4 for L ≥ 2.5·10⁵ (0.217). The old values were 419σ_g + 160, 53632σ_g/L, and 54688.
  - (R-member) l.256 drops the segment cubes. It now joins each cross group h ∈ G through its dom P's cubes and each W ∈ 𝒲^×(G) through T_W ⊆ X_W ∪ (the cubes meeting ℐ(W)). The old text had no join for a cross span member of single-loop groups, and this closes that too.
  - l.257 now has 1685σ(D_G) + 160, 215680σ(D_G)/L, and (219024ν_f + 1672ν_e)/L ≤ ν_r/4, with (219024·17/16 + 209)/10⁶ ≤ 0.233.
  - l.572 and l.696 are updated to match: 6(8496·17/16 + 11)/L₀^× ≤ 0.055, 215680/L₀^× ≤ 0.22, and the R-made cross term is now part of 8320u_Dσ(D)/L.
  - l.697 now says it is the 8M-neighbourhood of a π_j-cube that can meet 2^d cubes one step later.
- **TL-Rh-2 (MINOR, a gap), repaired.** l.844's growth factor 1 + y^s_k for single-loop insertions with h(D) = ∅ was booked only in D2.6 5.3 and in the dev recursion. The wrap(j) insertions are carried in (ii) outside both.
  - l.844 now adds: their masses gain Π_k(1 + y^s_k) ≤ e^{C_sS^R} ≤ 2, by y^s_k ≤ C_sϑ_k and C_sS^R ≤ log 2.
  - l.893's C_w now absorbs the factor 2. w̄'s form is unchanged.
- **TL-Rh-3 (MINOR), repaired.**
  - l.286 now lists the cost e^{5p₀(g_k)/64} of the sets X^{(44)}, the small members' rounding included ((6B), *The volume*), in place of "p₀(g_k)/32 for the rounding".
  - l.617 now says X_D is counted by σ(D) for a big member and, for a small one, in #π_k(B_P) or in half of the joining D_P term.
- **9a's unchecked item, the species of D_g^× with a wrap slot member.** l.471 already replaces the T-step rules by (6B)'s at the R-steps. l.763 now says so, and D_g^× is cross(k).

Note → 6863887e7805 (948 lines). D2.7 unchanged (52921b7909c8). (R-round) part a needs its next round: `scope_twoloops_Rround10a.md`. Scope `scope_twoloops_Rmember1.md` is updated for the l.256–257 constants.

## (R-round) Round 10a: Triage (3 November, 21:14–21:16)

Round 10a ran 20:59–21:14 (`referee_cli_20261103-205949_scope_twoloops_Rround10a.json`). It found no ERROR and two MINORs. It confirmed:
- TL-Rh-1: E_D without segments is closed-connected for every kind of member, and the counts at l.257, l.571, l.572, and l.696 check.
- TL-Rh-3 and l.763.
- The single-loop part of TL-Rh-2.
- The constants of *The count*, *The rates*, *The rooted sum*, *Joins*, and both cases.
- All the pins.

TL-Ri-1 is an accounting gap, so the round is not clean.

- **TL-Ri-1 (MINOR, an accounting gap), repaired.** l.893's C_w absorbed one R-step factor where more are stated.
  - l.842's doubling, for the groups with a wrap member, was in neither C_w nor w̄.
  - l.842's per-group bound "at most 1" was not summable in K.
  - The two-loop wrap insertions (l.467, and l.250's D_G with a wrap member) are cross lineages and gain 1 + y^R_k (l.773). The wrap sums did not list this.

  Repairs:
  - l.842 now bounds it as l.841 does. B(g) carries e^{−p₀(g_k)/2}, so these D_g add at most e^{−p₀(g_k)/4}w(W₁) per R-step, and the wrap masses gain at most Π_k(1 + e^{−p₀(g_k)/4}) ≤ e^{S^R} ≤ 2 ((H^R)).
  - l.893's C_w now absorbs three factors, at most 8 in all: Π(1 + y^s_k) ≤ 2 (l.844), Π(1 + y^R_k) ≤ e^{C_yS^R} ≤ 2 for the two-loop ones, and e^{S^R} ≤ 2 (l.842). w̄ is linear in C_w, so its form is unchanged.
- **TL-Ri-2 (MINOR), repaired.** l.256's (H2) for E_{D_G} now joins every group h ∈ G, single-loop groups included, through its dom P's cubes. For a single-loop group the reason is D_g's (H2) (l.707), with ℐ(h) = span(h).

Note → 76cf519ad1d4 (948 lines). D2.7 unchanged (52921b7909c8). (R-round) part a needs its next round: `scope_twoloops_Rround11a.md`.

## (R-round) Round 11a: Triage (3 November, 21:31–21:35)

Round 11a ran 21:16–21:31 (`referee_cli_20261103-211551_scope_twoloops_Rround11a.json`). It found no ERROR and one MINOR. It confirmed:
- TL-Ri-2.
- TL-Ri-1 for the single-loop first wrap members.
- The counts, the constants of (iv), and all the pins.

TL-Rj-1 is an accounting gap, so the round is not clean.

- **TL-Rj-1 (MINOR, an accounting gap), repaired.** l.842's per-step bound e^{−p₀(g_k)/4}w(W₁) holds only when the first wrap member W₁ is single-loop. A two-loop W₁ (l.467) has up to 19Mσ(W₁) link positions, so the D_G holding it add up to y^R_k·w(W₁) (l.264–269), even when W₁ is not their first cross insertion.
  - l.842 now separates the two cases: e^{−p₀(g_k)/4}w(W₁) for a single-loop W₁ (one arc in span(g), summed from one traversal), and y^R_k·w(W₁) for a two-loop one. Over the R-steps this gives Π_k(1 + e^{−p₀(g_k)/4})(1 + y^R_k) ≤ e^{(1 + C_y)S^R} ≤ 4.
  - l.893's C_w now absorbs at most 16 in all.
  - The referee's related point, the rate of the two-loop wrap insertions: l.722 now says the cross insertions under the rate λ_nν_r are all those with intervals on both loops (l.713), the two-loop wrap and att ones of l.467 and the merged ones included, and that their (S-w) weight e^{ν_rσ_j} dominates e^{λ_nν_rσ_j}. l.363 now names the two-loop insertions of single-loop species.
  - The referee's unreviewed aside, the two-loop att(j, ·) insertions as cross lineages, gaining 1 + y^R_k in D2.6 5.3's register: l.844 now has M_k ≤ (1 + δ_{k−1})(1 + y^s_k)(1 + y^R_k)M_{k−1}, with the lemma under C_δc̄S_R + (C_s + C_y)S^R ≤ log 2. l.286's conditions list is updated to match.
- **l.5 (peer input, 21:2x), corrected.** The large-field note defines C_H := C(d)(1 + log L)^pC_H^{reg}, with C_H^{reg} "the bulk constant", and does not bound C_H^{reg}. The table's "C_H ≤ C(d)(1 + log L)^p needed" (l.232) is a requirement. l.5 had stated it as derived.
  - l.5 now states C_H's definition and that (K0) is derived, not reviewed, in θ := C_H^{reg}θ_B.
  - It also states that the bound C_H ≤ C(d)(1 + log L)^p, that is, C_H^{reg} ≤ C(d)(1 + log L)^{p′}, is OPEN.
  - The peer owns C_H and is deriving it. Scope A7 is updated.

Note → 61dec64c6fd3 (948 lines). D2.7 unchanged (52921b7909c8). (R-round) part a needs its next round: `scope_twoloops_Rround12a.md`.

## (R-round) Round 12a: Triage (3 November, 21:47–21:54)

Round 12a ran 21:34–21:46 (`referee_cli_20261103-213403_scope_twoloops_Rround12a.json`). It found no ERROR and one MINOR. It confirmed:
- TL-Rj-1 for the wrap lineages: l.842's two cases, l.893's total of 16, l.844's recursion, and l.286's condition.
- The counts, the constants, and the pins it read.

TL-Rk-1 is an accounting gap that needed an argument, so the round is not clean.

- **TL-Rk-1 (MINOR, an accounting gap), repaired.** The R-made descendants (D_g^×, D_G) of a two-loop att(j, ·) first cross member W₁ had two registers in the text:
  - 5.3's register, at l.766 and l.844;
  - M^cr, at l.250, l.687, l.713, and l.781.

  In 5.3 they lacked D2.6 5.0's extent weight, which the later T-step bridge (T3) needs, and a second cross member's extent increase was not paid. The referee also noted that the λ_n rate for these lineages needs 5.5's slack.

  Repair: one register, W₁'s, in D2.6 5.3, with the later growth paid from W₁'s extent weight.
  - l.844: the descendants carry no extent weight and are carried by the cross carry lemma's step, without a bridge. Over the m = K′ − k later steps they grow by at most 2(1 + C_δc̄)^m ≤ 2L^m ((7), *The carried cross total*), and at the R-step their mass is at most y^R_k·w_{k−1}(W₁) ((6B), *Second case*).
  - W₁ has intervals on both loops, DL^m step-k units apart. So Y_{W₁} has a cube at least DL^m/(2M) − 1 π_k-sides from Coll_j, and its production extent weight, which dominates the later ones, gives w_{k−1}(W₁) ≤ e^{(3/8)ν_e}e^{−aL^m}w(W₁), with a = 3ν_eD/(16M).
  - By xe^{−ax} ≤ e^{−a}(1 + 1/a) for x ≥ 1 ((7)) and D ≥ 1 (l.310), the descendants add at most C_atty^R_k·w(W₁) over their lifetime, with C_att := 2e^{(3/8)ν_e}(1 + 16M/(3ν_e)).
  - 5.3 then runs with M_k ≤ (1 + δ_{k−1})(1 + C_sϑ_k)(1 + C_atty^R_k)M_{k−1}, under C_δc̄S_R + (C_s + C_attC_y)S^R ≤ log 2 (l.286, l.844), a smallness of g after M.
  - l.250, l.687, l.713, l.781, and l.784 now name the register: M^cr, or W₁'s 5.3 register for a two-loop att first member.
  - l.722: the two-loop att insertions keep D2.6 5.0's full weight, with the extent weight, in their register, and the two-loop wrap insertions keep their (S-w) weight. Both dominate w_n, so the rate λ_n needs no 5.5 slack, and their R-step payments are made from w_n.
- **Self-check (the referee's "1 + (c_r/(eν_r))ϑ_k"), repaired.** At full weight, a two-loop wrap or att insertion with h(D) = ∅ has no rate decrement for l.772's bound. Its options carry at most (1 + η(D)e^{−ϑ_kν_rσ})e^{ν_rσ}‖D‖ ≤ (1 + C_sϑ_k)e^{ν_rσ}‖D‖.
  - l.844 states this.
  - 5.3's factor 1 + y^s_k becomes 1 + C_sϑ_k ≥ 1 + y^s_k.
  - The wrap factor at l.844 and l.893 is now Π(1 + C_sϑ_k) ≤ e^{C_sS^R} ≤ 2, for single-loop and two-loop wrap insertions alike.
  - The condition is unchanged, since Σϑ_k ≤ S^R.

Note → 3cb431ac8449 (948 lines). D2.7 unchanged (52921b7909c8): its 15.5(i) sentence on the single-loop growth 1 + y^s_k still holds. (R-round) part a needs its next round: `scope_twoloops_Rround13a.md`.

## (R-round) Round 13a: Triage (3 November, 22:06–22:09)

Round 13a ran 21:54–22:05 (`referee_cli_20261103-215347_scope_twoloops_Rround13a.json`). It found one ERROR and one MINOR. It confirmed:
- The single register of every R-made insertion.
- The cross carry lemma's step for the descendants, with no bridge or extent weight.
- l.722's dominance.
- The self-check factor 1 + C_sϑ_k, with C_s's slack covering the margin e^{−(3/4)ϑ_kν_rσ}.
- The counts, *The count*, the constants, and the pins.

- **TL-Rl-1 (ERROR), repaired.** The 12a repair took the decay e^{−aL^m} from W₁'s extent weight, by "Y_{W₁} has a cube at least DL^m/(2M) − 1 π_k-sides from Coll_j". That is false. ext^{coll} is measured from the global collar Coll_j, which can cover Y_{W₁}: the referee's example is a strip of Λ_jᶜ along W₁'s domain, from loop to loop.

  The decay now comes from the descendants' own σ. Each R-made descendant D (D_g^×, D_G) has a closed-connected S_D meeting both loops, which are DL^m step-k units apart, with diam(S_D) ≤ 19Mσ(D) (u ≤ 19). So σ(D) ≥ DL^m/(19M).
  - The descendants and their own descendants are carried at the rate (λ_n − 1/32)ν_r. The cross carry lemma's budget (15/16)ν_rσ is within it, since λ_n ≥ 1 − S^R ≥ 31/32 (l.496).
  - The change of rate gives e^{−(ν_r/32)σ(D)} ≤ e^{−aL^m}, with a := ν_rD/(608M).
  - With the growth 2L^m and the mass y^R_kw(W₁) at the R-step, they add at most C_atty^R_kw(W₁) over their lifetime, with C_att := 2(1 + 608M/ν_r) by D ≥ 1.
  - The condition C_δc̄S_R + (C_s + C_attC_y)S^R ≤ log 2 (l.286) is unchanged in form, a smallness of g after M.
  - l.844's self-check sentence now states the margin as e^{−(3/4)ϑ_kν_rσ}, after l.264's payments, with 4c_r/(3eν_r) ≤ C_s.
- **TL-Rl-2 (MINOR), repaired.** D2.7 15.5(i)'s sentence on how η(D) is paid now:
  - lists the two-loop wrap or att insertion with h(D) = ∅, at full weight, as a growth 1 + C_sϑ_k;
  - replaces the stale pin "(l.10)" with "(its (6B), *15.5*)".

  D2.7 → 4fdca0fc2af1 (236 lines); peer notified (22:08).

Note → 4098316bc887 (948 lines). (R-round) part a needs its next round: `scope_twoloops_Rround14a.md`.

## (R-round) Round 14a: Triage (3 November, 22:24–22:30)

Round 14a ran 22:08–22:23 (`referee_cli_20261103-220830_scope_twoloops_Rround14a.json`). It found one ERROR and one MINOR. It confirmed:
- σ(D) ≥ DL^m/(19M), a, and C_att.
- The T-step budget at the shifted rate.
- W₁'s bridge, and that no other line uses W₁'s extent.
- The h(D) = ∅ factor 1 + C_sϑ_k and its booking.
- D2.7 15.5(i).
- The counts, the constants, and the pins.

- **TL-Rm-1 (ERROR), repaired.** The shifted descendants of W₁ kept the rate λ_n − 1/32. The R-step payments (l.264, l.731, l.772) still assumed the rate λ_{k−1}. A shifted D can be a non-first member of a later group in M^cr, after an earlier cross(j′), j′ < j, in D2.0(3)'s order. There it was short by e^{(1/32 − ε_k/4 − 3ϑ_k/4)ν_rσ(D)}.

  The shift is now a property of each insertion, inherited by the insertions it enters (l.722, *The rates*): w_n(D) := e^{λ_n(D)ν_rσ(D)}e^{θ(D)}‖D‖, with λ_n(D) := λ_n − s(D)/32 and s(D) ∈ {0, 1}.
  - s(D) = 1 for an R-made insertion whose first cross member is a two-loop att insertion that 5.3 carries.
  - s(D) = 1 for an R-made insertion with a member of shift 1.
  - s(D) = 1 for a touched or merged descendant of a shift-1 insertion.
  - Otherwise s(D) = 0.

  So λ_k(D_g^×) ≤ λ_k(W) for each cross member W, and λ_n(D) ≥ 15/16. The payments now read with λ_k(D_g^×) and λ_k(D_G):
  - l.731 and l.264: "≤ w_{k−1}(W)e^{−…}, since λ_k(·) ≤ λ_k(W) = λ_{k−1}(W) − ε_k − ϑ_k".
  - l.250, l.259, l.713, l.793: the rate λ_k(D_G) or λ_k(D_g^×).
  - l.374, l.780: the rate λ_k(W).
  - l.485, l.496: the cross carry lemma at the rates λ_{n+1}(D), with budget (15/16)ν_rσ ≤ λ_n(D)ν_rσ.

  l.844 now states that the shifted insertions pay from their own weights at later R-steps and pass the shift on. A lower rate only lowers the weights the second-case sums (l.770) and A^× bound, and the weight still dominates the norm.
- **TL-Rm-2 (MINOR), repaired.** l.844's recursion is now stated for the majorant M̂_k := P_k + Σ_{k′≤k}C_atty^R_{k′}P_{k′−1}.
  - P_k is the register's mass without the shifted descendants.
  - Σw(W₁) ≤ P_{k′−1}.
  - P_k ≤ (1 + δ_{k−1})(1 + C_sϑ_k)P_{k−1}.
  - So M̂_k ≤ (1 + δ_{k−1})(1 + C_sϑ_k)(1 + C_atty^R_k)M̂_{k−1}, and 5.3's lemma holds for M̂ under the same condition.
- **l.5 (outside this packet), requoted after the peer's message.** LF 7233fdd32c4d l.6 now states C_H^{reg} ≤ C(d)(1 + log L)^{p′}, with constants of d only, by (K0)(f) (derived, not reviewed). So l.5 now reads C_H ≤ C(d)(1 + log L)^{p+p′}, derived, not reviewed, and it notes A_♮ at the interfaces j ≥ 1. Scope A7 is updated to match.

Note → d1c618ec76c2 (948 lines). D2.7 unchanged (4fdca0fc2af1). (R-round) part a needs its next round: `scope_twoloops_Rround15a.md`.

l.5, during round 15a (outside its scope): A_♮ = A_N is now quoted with its exact scope from LF l.1009 {#K0.g6} (vi), after the peer's message: "at the points of R₀ outside the blocks of Λ₁ that meet R₁". Note → bf3811b20951.

## (R-round) Round 15a: Triage (3 November, 22:43–22:47)

Round 15a ran 22:28–22:42 (`referee_cli_20261103-222841_scope_twoloops_Rround15a.json`). It found no ERROR and two MINORs, both real gaps in the bookkeeping, so another round is needed.

It confirmed TL-Rm-1's repair:
- The shift is well defined, never compounds, and keeps λ_n(D) ≥ 15/16.
- The R-step payments at l.264, l.270, l.731, l.769, and l.772 hold, the h = ∅ case included.
- l.467's full-weight insertions are consistent.
- The T-step budgets fit: 15/16 for a first member, and 25/32 for a non-first member, merge extent included.
- (7) and (8.2) survive.

It also confirmed σ(D), C_att, the h(D) = ∅ factors, the dev recursion, D2.7 15.5(i), the counts, the constants, and the pins.

- **TL-Rn-1 (MINOR), repaired.** The claim "Σw(W₁) ≤ P_{k′−1}" left out the T-step into k′. M̂_k now has C_atty^R_{k′}(1 + δ_{k′−1})P_{k′−1}, with Σw(W₁) ≤ (1 + δ_{k′−1})P_{k′−1} (5.3). The recursion is unchanged by this.
- **TL-Rn-2 (MINOR), repaired.** l.841 booked case (b)'s lineage growth e^{−p₀(g_k)/4}w(W₁) in 5.3's δ_k, which 5.3 spends on the next T-step.
  - l.841 now books it as a growth 1 + ε_k of the register at the R-step k.
  - In l.844, P_k ≤ (1 + δ_{k−1})(1 + C_sϑ_k)(1 + ε_k)P_{k−1}.
  - The recursion is M̂_k ≤ (1 + δ_{k−1})(1 + C_sϑ_k)(1 + ε_k)(1 + C_atty^R_k)M̂_{k−1}.
  - The condition is C_δc̄S_R + (1 + C_s + C_attC_y)S^R ≤ log 2 (l.286, l.844), by Σε_k ≤ S^R.
- **Not settled by the referee: CRE p.245's line.** The transcription p245_corrected.tex opens with a "%" line. "R_0 ≥ (log g_0^{−2})^r, r ≥ 2" is on its file l.34, with the sentence starting on l.33. That is printed l.32–33, as the note cites (l.776), provided file line N is printed line N − 1 on this page. No change.

Note → 735dc3ab5548 (948 lines). D2.7 unchanged (4fdca0fc2af1). (R-round) part a needs its next round: `scope_twoloops_Rround16a.md`.

## (R-round) Round 16a: Triage (3 November, 22:58–23:01)

Round 16a ran 22:44–22:58 (`referee_cli_20261103-224418_scope_twoloops_Rround16a.json`).

It found no ERROR and one MINOR, which is a wording/attribution minor. Under the clearance rule, round 16a is the **first clean round** of part a.

It confirmed:
- TL-Rn-1's M̂ bounds the register at every step.
- TL-Rn-2's booking holds: every R-step growth is booked once, and none is in δ_k.
- The recursion, 5.3's lemma for M̂, and the condition agree at l.286, l.841–844, (7), and D2.7 15.5(i).
- The shift, the counts, all the constants (recomputed), the (R-round) block, and the pins hold.
- CRE p.245's pin l.32–33 holds under the convention file l.N = printed l.N − 1.

Findings and repairs:
- **TL-Ro-1 (MINOR, wording), repaired.** l.699 put the paraphrase "a slot inside Z′'s activity" in quotation marks. It now quotes D2.7 15.5(i) (l.175): "a slot inside their activity", the activity of the polymers of its home, here P.
- **Outside the packet (repaired): D2.7 15.8 (l.191).** It stated D26's carry lemma past N under C_δc̄S_R ≤ log 2 alone. A sentence now adds the R-step factors that the att registers gain:
  - 1 + y^s_k ≤ 1 + C_sϑ_k for the options with h(D) = ∅;
  - 1 + ε_k for the lineage growth at an R-step.

  So the lemma holds under C_δc̄S_R + (1 + C_s)S^R ≤ log 2 for one loop, and under l.286's condition for the pair. D2.7 → 5ba3bd34f250 (236 lines); peer notified (22:59).
- **Outside the packet (not changed): D2.6 5.0's CRE p.245 pin.** It reads "l.34", which is the file line; the printed line is l.33.

Note → 9118b6641c9d (948 lines). (R-round) part a needs its second clean round: `scope_twoloops_Rround17a.md`.

## (R-round) Round 17a: Triage (3 November, 23:16–23:20)

Round 17a ran 23:00–23:16 (`referee_cli_20261103-230004_scope_twoloops_Rround17a.json`) and was **CLEAN**: no ERROR and no MINOR.

**Part a is cleared after two clean rounds, 16a and 17a.**

17a confirmed the following:
- l.699's quote;
- D2.7 15.8's new sentence: one loop gains exactly 1 + C_sϑ_k and 1 + ε_k and no shift-1 descendants, and the pair adds C_attC_y;
- M̂ and the shift;
- every count and constant, recomputed.

The referee could not render pages (shell denied). It flagged two pin sets as unverified: l.728's CRE p.251 l.39–40 and l.645–652's LFR II p.389 lines.

I rendered the scans (CMP 119 pdf pp.8, 9, 26; CMP 122b pdf pp.14, 35) and counted the printed lines. Those pins were transcription-file lines, and the transcriptions reflow the text around displays. They are now anchored to the printed displays:
- **l.644:** p.389 l.12 → the sixth line below (1.94).
- **l.645 and l.648:** l.27–28 → the three lines after (1.95).
- **l.648:**
  - l.32–41 → (1.96) and the three lines after it;
  - l.41 → the second line above (1.97).
- **l.649:**
  - l.13–14 → the eighth line below (1.94);
  - l.16 → the display after "g_k is so small that".
- **l.650:** l.32–33 → (1.96).
- **l.728:**
  - LFR II p.368 l.23 → (1.47);
  - CRE p.250 l.47 → the third line below (1.19);
  - CRE p.251 l.39 → the eighth line below (1.21);
  - CRE p.268 l.41 → the fourth line below (3.17);
  - p.251 l.39–40 → the eighth and ninth lines below (1.21);
  - p.250 l.47–48 → the third to fifth lines below (1.19).

These are attribution changes to a cleared packet, so they get one check round: `scope_twoloops_Rround18a.md`. The rendered pages are given to the referee as PNGs.

Note → b7ea6c10149d (948 lines).

**Correction (23:2x).** The line-pin convention is the file line of pNNN_corrected.tex (scope A7 l.86–87). The raw pNNN.tex has one more line, its pagemark. The rule "file line N = printed line N − 1" in the 15a triage and in scopes 16a and 17a was mine, and it was wrong.

Under the file-line convention, CRE p.245's "R_0 ≥ (log g_0^{−2})^r, r ≥ 2" is at l.33–34. l.776 cited l.32–33, so it now cites p.245 l.33–34. D2.6 5.0's "l.34" is correct after all.

The other pins that 16a and 17a checked hold under the file-line convention: LFR II p.376 l.10–13, RG I p.251 l.14 and p.257 l.14–16, LFR I p.179 l.7–11, and CRE p.246 l.24–25. I re-read each.

The display anchors at l.644–650 and l.728 are not line pins, so the convention does not affect them.

Note → 370d600a46dc (948 lines).

## (R-round) Round 18a: Triage (3 November, 23:30–23:32)

Round 18a ran 23:19–23:22 (`referee_cli_20261103-231947_scope_twoloops_Rround18a.json`). It checked the re-anchored pins on the rendered scans. It found no ERROR and one attribution MINOR, so the round is clean under the clearance rule.
- **The MINOR (repaired):** l.728 cited "CRE p.250, the third line below (1.19)" for the form B₃exp(−δ·). That row ends "< O(1)B₃", and the exponential is on the fourth row. It now reads "the third and fourth lines below (1.19)".
- **Confirmed on the scans:** every other pin points at the print it supports, and every quote is verbatim. This covers p.389 (below (1.94), after (1.95), (1.96), above (1.97)), p.368 (1.47), CRE p.251 below (1.21), CRE p.268 below (3.17), and CRE p.250's M₂R₁ statement.

**(R-round) part a is done.** Two clean rounds (16a, 17a) cleared it, and one check round (18a) cleared the pins.

Note → 67431b261a98 (948 lines). Next in the queue: R-eval A7 (`scope_twoloops_RevalA7.md`).
