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
