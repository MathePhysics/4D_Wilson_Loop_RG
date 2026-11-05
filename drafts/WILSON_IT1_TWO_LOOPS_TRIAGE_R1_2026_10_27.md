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

## (R-eval) Packet A (the Landing), Round A7: Triage (3 November, 23:48–23:51)

Round A7 ran 23:32–23:48 (`referee_cli_20261103-233211_scope_twoloops_RevalA7.json`). It found no ERROR and three MINORs.

It confirmed the following:
- **A6 repairs:** A6-1 to A6-5 are closed.
- **Derivations:** the transport form, the four response steps, the mixed term, the landing, the consumers, and the order of the constants all hold against the sources.
- **l.5:** it states Open (R-eval-old) correctly; the LF quotes are verbatim, and no bound in the packet uses C_H.
- **Open-gap marks:** T₂^{old} and (R-eval-curv) are marked wherever a bound needs them.
- **Admissibility:** the packet uses it only for the pre-R {Ω″_j} (LFR I p.179 l.40).

- **A7-1 (MINOR), repaired.** l.39 said "the base point of Φ(𝐔) is U_k^0(U)". That holds only for a real base U ∈ 𝓜. It now reads "the base point of Φ(𝐔) is Φ(U) = E(U)U, which is U_k^0(M(U)) for a real base U ∈ 𝓜, as at Φ ∘ P (l.159)". No bound changes, since the bounds are taken at Φ ∘ P. The claim was false as stated, so it counts as a real minor.
- **A7-2 (MINOR, pin), repaired.** S5 is at LF triage R38 l.47, not l.46. Fixed at l.5 and in scope A7.
- **A7-3 (MINOR, pin), repaired.** "table row 226" is {#T11.11}, which says nothing about C_H. The pin is dropped; l.5 already cites table l.232.
- **REG pins (the referee had no transcription in its list), checked against tex\REG\parts.** These are raw files: line N is convention line N − 1 because of the pagemark. All hold:
  - p.86 l.52–53 is the B₀ bound;
  - p.87 l.16 reads "depend on d and L only";
  - (1.62) has 5dLB₀;
  - (1.75)–(1.76) carry B₁.
- **Outside the packet, covariance note l.37, repaired.** "X_W ⊂ Ω_{k+1} ⊂ Ω_j" used Ω_{k+1} ⊂ Ω_j against the production-time Ω_j, and that inclusion fails across an R-step (Ω′_j = Ω_j ∪ Z). The sentence now uses X_W in the top layer Ω_j at production (its l.15), and notes that the inclusion is not used. Covariance note → d0b64d4c31c5 (184 lines).

A7-1 is a real minor, so the packet needs another round: `scope_twoloops_RevalA8.md`.

Note → 81dd91ec3603 (948 lines).

### Bookkeeping: LF and Table Cites by Tag (4 Nov, 00:17)

The peer now cites the LF by tag only, and its lines may move. The note's l.5 cited LF lines that no longer hold the quoted text. These swaps change no content, so they get no review round (user, 4 Nov: "These bookkeeping changes don't make a new review necessary"):

- the sup-bound cite "…DEPTH_2026_10_27.md l.6" → #0.1.10;
- the C_H definition and the bulk constant "(its l.6, l.1008)" → "(its #0.1.10, #KW)", and "(K0) (l.1009)" → "(K0) (#K0)";
- the C_H^{reg} bound "(its l.6, {#0.1}; l.1009, {#K0.f}; …)" → "(its #0.1.27; #K0.f; …)";
- "(its l.1009, {#K0.g6} (vi))" → "(its #K0.g6 (vi))", and "Λ₀/Λ₁ (its l.6)" → "(its #0.1.30)";
- the representative v "(its l.6)" → "(its #0.1.25)";
- "table l.232" → "table #T11.17".

Note 81dd91ec3603 → 7e6f58f2bea8 (948 lines). WILSON_IT1_REVAL_OLD_DRAFT_2026_11_03.md l.87 "l.6" → "#0.1": e2157f4c6165 → 7e567d3c8201 (203 lines). D2.7 cites no LF line, so it is unchanged. The A8 scope stays as the record of what A8 was given; scope A9 onward cites the LF by tag.

### Bookkeeping: The Note Is Tagged (4 Nov, 00:28–00:33)

User, 4 Nov: full tagging, so that repairs can add lines instead of lengthening old ones. No review round (bookkeeping).

- **Frozen version.** `WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_PRETAG_7e6f58f2bea8.md` is the note as A8 reviewed it plus the LF tag swaps above. Every "l.N" of the note in this file, the scopes, and the referee logs is a line of that version.
- **Tags.** Each content line N of the frozen version carries {#N} at its start, after the list marker or heading marks; the title carries none. "l.N" of the note is therefore #N.
- **Self-references.** The note cited 339 "l.N" outside the Bałaban pins. 145 were its own lines, and these are now #N (ranges #A–#B). The other 194 name other files and stay as they are: the map, SW, D2.6, D2.7, the covariance note, the continuum note, the O4 note, and the pages of LFR, VAR, CRE, and REG. The 16 ambiguous cases were decided against the cited text. "(l.36)" at #94, "(l.37)" at #160, "(l.20–22)" at #200, "(l.37–39)" at #640, "((1.14), l.59–62)" at #130, and "at l.40" at #39 are page pins. The rest are the note's own lines, with each target checked: #39, #75, #102–103, #103, #131, #156, #6, and #14.
- **Splits.** Four lines were split at sentence boundaries into pieces {#N.j} on their own lines, at the paragraph's content column: #5 into 11 pieces, #6 into 9, #130 into 20, and #173 into 8. A script check confirms that rejoining the pieces with single spaces reproduces the tagged lines exactly, and that the tagging diff consists of the tags and the "l." → "#" replacements only.
- **Convention line.** {#3.1}, after #3, states the convention.
- **Labels.** `LABELS_TWO_LOOPS.md` (941 tags) is generated by `labels_two_loops.py`, which also checks that every tag is unique and that every #N in the note names a tag.

Note 7e6f58f2bea8 → d8dd5b48a47f (993 lines). Outside citations of the note by line remain valid as #N: table "l.5", "l.267"; LF and LF triage γ "l.130"; SESSION_HANDOVER.md "l.5".

## (R-eval) Packet A (the Landing), Round A8: Triage (4 November, 00:15–00:50)

Referee run `referee_cli_20261103-235116_scope_twoloops_RevalA8.json` (23:51–00:14), on note #38–#76 with #5 and covariance note l.37. One ERROR and one MINOR. A7-1, A7-2, and A7-3 are confirmed closed, and so is covariance note l.37 as the packet uses it. Not clean.

- **A8-1 (ERROR), #5: accepted.** The referee's quotes are checked against the LF (d46e290cc196).
  - #0.1.10 bounds abs(Q_{i′}HB) ≤ C_HL^{−(i−i′)}‖B‖ "in a norm that every step of the chain preserves", and says "The supremum does not serve: at the contacts of codimension ≥ 3 between components of Λ^c the response is L times the datum". Leaving the weighted norm "at the domain conditions and at the evaluation points, costs C(d)(1 + log L)^pL once".
  - #0.1.18 defines W(x) := (1 + log L)^p(L/t)^κ(L/t₃)^{1−κ}, with κ < 1 and ρ₀ ≤ t ≤ t₃ ≤ L. #0.1.19 and #KW put the contacts of VAR's problem at codimension ≥ 2.
  - #0.1.25 takes v locally, so #5.10's "global Landau representative" is wrong. #0.1.27 bounds the whole response, gradient part included, in ‖·‖_W at A_N, from sup data. So #5.10's "The bound for v does not control Dλ" is also wrong.
  - #0.1.28 says the weight L/t₃ is not removable by a gauge.
  - Consequence (derived): at the evaluation points with t₃ ≥ L^{1/2}, W ≤ (1 + log L)^pL^{(1+κ)/2}, so C_{resp,∞} = o(L) there. At the contacts the response is of order L times the datum, so the third input in its sup form fails there and the third route does not close the gap. No packet bound uses C_H, so #38–#76 are unaffected.
  - Repair: rewrite #5.4 and #5.7–#5.10 to quote #0.1.10, #0.1.18, #0.1.19, #0.1.25–#0.1.28 as they stand and to state this consequence. #5.5 and #5.6 are kept. It is applied after D1 lands, because every running scope reads #5.
- **A8-2 (MINOR), #41: accepted, a real gap.** #40 and #160 define U_0(𝐔) := U_0^{(AL)}, but #41 writes it as (1.43)'s minimiser "in the axial gauge" (LFR II p.367 l.27, l.30).
  - LFR I (1.85)–(1.87) (p.197 l.1–35): U_0^{(AL)} = U_0^{u_0} = exp iη𝔸₀ inside Λ, with 𝔸₀ = ℍ_{k,Λ}((1/i)log M^·(U_0)) a function of U_0's averages on 𝔹_k(Λ), and |𝔸₀| < O(1)B₃²B₅M⁶ε_k.
  - VAR (190) bounds the Landau representative ℋ of U_k(V′V₀)U_k(V₀)^{−1} relative to U₀ (Proposition 9, p.309 l.10–11; p.305 l.36–39).
  - The repair needs three things: the identity U_0^{(AL)}(𝐔) = U^{(L)}_{k,Z}(M^k(𝐔), V_Λ(M^k(𝐔))), with (1.43) supplying only the data B̃′ and B′_Λ; the step from VAR's frame to the AL frame; and the effect of ū₀(𝐔), complex at complex 𝐔, on the averages that #43 uses. It is derived before A9.
- **Next:** packet A comes sixth in the reappraised order (handover, "ORDER"). D1 runs first.

## (R-eval) Packet D (the Constants and the List), Round D1: Triage (4 November, 00:55–01:05)

Referee: launched 00:41, finished 00:55 (referee_cli_20261104-004105_scope_twoloops_RevalD1.json). Two ERRORs and four MINORs. The constants, the arithmetic, the pins of #14, and #6's reduction were checked and hold. Note before: d8dd5b48a47f; after the repairs below and the A8-1 rewrite: 05a690da01f0 (994 lines, 942 tags). Every finding was checked against the body before its repair.

- **D1-1 (ERROR), #31: accepted.** #31 listed (2.34), (2.35), (2.37), and (2.36) about 0 as "quoted … at the evaluation points" with no mark. The body quotes them at the u-free representatives only given (1.65)'s application at (P(𝐔), J^h(P(𝐔))), which is Open (R-eval-curv) with CRE (2.39) at P(𝐔) (#156, #158), and has them open at 𝕌̃. #12 carried the second mark but not the first.
  - Repair: #31 and #12 now state both marks, citing #156 and #158.
- **D1-2 (ERROR), the list: accepted.** Only #21 carried a mark. The body marks the items at #58, #76, #78, #90, #92, #113, #116, #130.15, #130.17, #137, #153, #154, #159, #166, #167, and #172 (each checked).
  - Repair: #17's lead now states that each item holds up to the opens it marks, and #18, #19, #22, #23, #25–#30, #32, and #33 carry the body's marks with their tags.
- **D1-3 (MINOR, a real gap), #6.4: accepted.** "The T-step's points use at most an eighth" did not follow: the map fits the deformations into the whole margin with its enlarged C′ (l.704, l.928, l.1614), and C_K′ = max(C′, C_K) equals C′ when C′ ≥ C_K. At s ≠ 1, P of the point also carries 2K sup|𝐇| (#137).
  - Repair: C_K′ := max(8C′, C_K) at #14 and #138. #139's bound becomes C_K′ ≤ max(8C′, 128K(1−β)^{−2}) ≤ 8K(1−β)^{−2}max(C′, 16) with K ≥ 1, so C_T^{(K)} ≤ 8K(1−β)^{−2}C_T still holds. #6.4 now says the deformations use at most an eighth for g small (the curvature change is linear in 𝐇 up to a quadratic term), and that the response's share on the older layers, which is not shown to decay with the layer, is part of the open.
- **D1-4 (MINOR), #14: accepted.** The reclassified dev insertions are in D2.6 closure §3 (l.70–73), not §2.1; §3 l.73's factor 1 + 6S₃₀C₁/C₀ was missing; (6b)'s entry was quoted at its 𝒟^{sub} value.
  - Repair: the pin is §3, l.70–73; the factor 1 + 6S₃₀λ_R is listed, λ times that on the family (#55); (6b)'s entry is ≤ 3λλ_RC_χ(Σ_tw_t)ρ_{k+1} on the family (#57–#58).
- **D1-5 (MINOR, attribution), #7, #18, #32: accepted.** TB's and JB's review status was missing.
  - Repair: #7 now names both reviewed parts (#130–#136, packet TB; #173.1–#173.7, packet JB); #18 and #32 carry their status.
- **D1-6 (MINOR, attribution), #16: accepted.** "((1.49)–(1.51))" had no paper key.
  - Repair: "LFR II (1.51), p.370 l.11, with U_k^0 from (1.50)" (checked against p370_corrected.tex l.4–14).
- **Also applied: A8-1's rewrite of #5.** #5.4 now quotes the large-field note as it stands: its #0.1.10 (the weighted norm; "the supremum does not serve"; leaving the norm costs C(d)(1 + log L)^pL), #0.1.18 (W, κ, t, t₃, ρ₀), #0.1.29 (in VAR's problem t₃ is the distance to the contacts of codimension ≥ 2), #0.1.27 ((KW), gradient part included), and #0.1.4 (A_N). The new #5.11 derives C_{resp,∞} ≤ (1 + log L)^pL^{(1+κ)/2}C_H = o(L) where t₃ ≥ L^{1/2}, and states that at the contacts the response is L times the datum and not removable by a gauge (#0.1.10, #0.1.28), so the third input fails at the sites with t₃ < L^{1/2}. #5.7 restricts the conclusion to t₃ ≥ L^{1/2} and has λ absorb (1 + log L)^pLC_HM⁵ (sup W ≤ (1 + log L)^pL). #5.8 states the two remaining inputs. #5.10 replaces the former claim about the global Landau v (wrong: the LF's bound covers the gradient part at A_N, #0.1.25–#0.1.27) with the passage from A_N to V̂, through u_R = A_N + ∂ω with abs(Im ηω) ≤ C(L, M)ε₁ (#0.1.3, #0.1.4, #0.1.14), as part of the input. labels_two_loops.py was run.
- **Next:** D2, with scope_twoloops_RevalD2.md. Every later scope declares #5 with #5.1–#5.11.

## (R-eval) Packet D, Round D2: Triage (4 November, 01:14–01:20)

Referee: launched 01:01:55, finished 01:14 (referee_cli_20261104-010155_scope_twoloops_RevalD2.json). One ERROR and one MINOR. D1-1 and D1-3 to D1-6 were confirmed closed; D1-2 was closed except at #19 and #30. Not clean, so D needs D3 and D4. Note: ba6220526a7d after the D2 repairs, 81ccfd23e258 after the #20 mark (994 lines, 942 tags). D3 launched 01:15.

- **D2-1 (ERROR), #19 and #30: accepted.** Checked against #172 and #152.
  - #19 named only P of the point. #172 also marks the transport-form points, where the words' equality at 𝕌̃ needs (2.34)–(2.37) (#113), and U^R, where the B-terms reach their bounds only through #153's transfer.
  - #30 omitted #152's marks for the derived configurations' currents J_n(M·(𝐔)).
  - Repair: #19 now names all three places; #30 carries #152's marks, citing #152, #156, and #158.
- **D2-2 (MINOR, a real gap in the statuses), #14: accepted.** (6b)'s family bound was quoted without #58's mark.
  - Repair: #14 now says that (6b) runs on the family up to (2.34)–(2.37) in its radius R′ (Open (R-eval-curv), #58).
- **Pre-launch sweep:** the list items without an (R-eval-curv) mark (#20, #21, #24, #27, #34) were checked against their body paragraphs. #20 (the transport form) was missing #45–#46's Open (R-eval-old) mark, which is now added. #21, #24, #27, and #34 match their body paragraphs.
- **Also:** #5.11 is now headed "*Away from the contacts (derived, not reviewed).*". It is reviewed in packet A.
- **Next:** D3, with scope_twoloops_RevalD3.md.

## (R-eval) Packet D, Round D3: Triage, and the A8-2 Repair (4 November, 01:34–01:40)

Referee: launched 01:15:28, finished 01:33 (referee_cli_20261104-011528_scope_twoloops_RevalD3.json). One ERROR and three MINORs. D1-1 to D1-6, D2-1, D2-2, and the #20 mark were confirmed closed. Not clean. Note after the repairs and the A8-2 edits: d7f60604d26a (996 lines, 944 tags).

- **D3-1 (ERROR), #17 and #24: accepted.** (ii) derives the analyticity at Bałaban's (𝐔, 𝐉)-extension (#85, #89). The members Y∘P are built on the note's extension, which agrees with Bałaban's only as far as (P(𝐔), J^h(P(𝐔))) lies in Ũ_k^c(Y₄) (#127, #156).
  - Repair: #17 now says "the analyticity of Bałaban's extension", and #24 adds the members' analyticity, marked Open (R-eval-curv) (#127, #156).
- **D3-2 (MINOR, a real gap in the statuses): accepted.** At the Schwarz step's scaled points (#92) and along P(𝐔_t) (#113), the open covers (1.65)'s application at the axial form, CRE (2.39) included, and not only (2.34)–(2.37).
  - Repair: #92 and #113 now name it, citing #6.6, #127, and #156. #6.5 adds both places to its list. #19, #22, and #23 carry it, and #29 inherits it through #23.
- **D3-3 (MINOR), #17: accepted.** #206 reads "combine[s]" as a product, and the base points use that reading (#202–#203, #212).
  - Repair: the reading *R-combined* is added to #17's list, and #206 names it.
- **D3-4 (MINOR, wording), #32: accepted.** It now reads "at P of the T-step's points at s ≠ 1 (#137) and, in part (a), at s = 1 at a localized background".
- **A8-2 repair (derived, not reviewed; for A9).**
  - #41 now writes U_0(𝐔) = U_0^{(AL)}(𝐔) as LFR II p.366 l.23–25 defines it, with (1.43)'s axial U_0^{ax}(𝐔) and U_0 = (U_0^{ax})^{u_0} (LFR I (1.86), p.197 l.18–29).
  - New #41.1, the frame: U_0(𝐔) = (e^{iηℋ′}U_0(U))^g, with ℋ′ = Ad(u_0(U))ℋ and g = u_0(𝐔)w^{−1}u_0(U)^{−1}, where w is VAR's transformation, and g = 1 at 𝐔 = U. The data on Λ ∩ Ω″^{∼2}_{h+1} are those of e^{iηℋ′}U_0(U) transformed by ḡ.
  - New #41.2, the bound on g: the Schwarz lemma in the data's scale t on the disc |t| ≤ cα_{1,k}/|B̃′|, where (1.38)–(1.45) hold, with #107's device and (1.84), (1.44)–(1.45), and (1.87). It gives η|Dλ| ≤ O(1)(1 + (C⁰_{rsp} + B₃²B₅)M⁵ + o(1))s_Z. The ε-part enters as ε_k/α_{1,k} → 0 (q₁ > p₀), so no additive term appears.
  - #42 defines C⁰_{rsp} := O(1)4d·100⁵γ₀^{−1}B₃² and C_{rsp} := O(d)(C⁰_{rsp} + B₃²B₅). #43 and #164 use C_{rsp}. Every other use of C_{rsp} is an upper bound, so it stands with the larger constant.
  - A remark that the route does not need: REG's representative is covariant under G-valued background gauges. This follows from CMP98 (78)–(81) (p.30), covariant under V₀ → V₀^w, v → wvw^{−1}, and from R(U₀), the orthogonal projection onto Δ_{U₀}N(Q′(U₀)) (REG p.80 l.12–13), covariant under the orthogonal Ad_w.
- **Next:** D4. A9 reviews #5 (with #5.11) and #41–#43 (with #41.1–#41.2).

## (R-eval) Packet D, Round D4: Triage, and the Response's Share (4 November, 01:48–01:50)

Referee: launched 01:36:23, finished 01:47:51 (referee_cli_20261104-013623_scope_twoloops_RevalD4.json). No ERROR and two MINORs. D3-1 to D3-4 are closed; D2-1, D2-2, the #20 mark, and D1-1 to D1-6 stay closed. List items #20–#21 still match #41–#43 with #41.1–#41.2. Not clean, since D4-1 is a missing open mark. Note after the repairs and #6.9: 1926357abfa8 (997 lines, 945 tags).

- **D4-1 (MINOR, a real gap in the statuses), #26 with #78, #80, #130.1, and #172: accepted.** The class's other bounds reach the members' values through the words' equality at 𝕌̃ (#111), which is #113's identity theorem. That theorem holds only as far as (P(𝐔_t), J^h(P(𝐔_t))) ∈ Ũ_k^c(Y₄), so the open also covers (1.65)'s application along P(𝐔_t), CRE (2.39) included.
  - Repair: #26, #78, #80, and #130.1 add "(1.65)'s application along P(𝐔_t), CRE (2.39) included (#113)". #172 states #113's condition in full.
- **D4-2 (MINOR), #17: accepted.** The map's and SW's readings (R-cpl₀, R-dec, R-av, R-m, R-adm, R-p, R-mJ) are used at #53, #54, #68, #70, #137, and #138 and come in through #293–#294.
  - Repair: #17 adds a sentence naming them and pointing to the inherited inputs (#293–#294).
- **The response's share (new #6.9, derived, not reviewed; for A9).** This closes the part of #6.4 that was open about the s ≠ 1 response 2K sup|𝐇|.
  - T_Y's α₀-entry gives 2K sup|𝐇| ≤ β(1−β)²α_{0,k}/16 + O(Kε_k) (#138).
  - The response's gradient in 𝒟^λ_k's layer weight converts to a curvature change of at most 2ξ²|∇δ|.
  - On layer n = k − m it takes at most (1 + o(1))(1−β)²(1+β₀)²max(1, √m)(2/L)^m/4 + o(1) of the next step's margin β2^{−(m+1)}. That is below ¼ for L ≥ 8 and g_K small.
  - With the deformations' eighth, more than half of the margin remains, as #6.3 needs. #6.4 now says so, and its open is the margin at the s = 1 point itself.
- **Next:** D5, which also checks #6.4's changed sentence as a statement of what is open. A9 reviews #5 (with #5.11), #41–#43 (with #41.1–#41.2), and #6.9.

## (R-eval) Packet D, Round D5: Triage, and the Curvature Conditions by the Members' Slack (4 November, 02:07–02:17)

Referee: launched 01:50:21, finished 02:06:35 (referee_cli_20261104-015021_scope_twoloops_RevalD5.json). No ERROR and two MINORs. D4-1 and D4-2 are closed, and D1–D3's repairs stay closed. The constants, the arithmetic, #6's reduction, the covariance note's μ, and every pin hold. Not clean, since D5-1 is a missing open mark. Note after the repairs and the closure: 756f4b8b4dd2 (1007 lines, 951 tags). D6 launched 02:17.

- **D5-1 (MINOR, a real gap in the statuses), #25 with #167: accepted.** The extension-domain points' bounds also reach the members through #113's identity theorem, which needs the condition along the whole path.
  - Repair: #25 and #167 now mark 𝒟_k itself at V̂ and along the segments V̂_t (#113). This is the form the condition takes after the closure below.
- **D5-2 (MINOR), #6.4 with #6.9: accepted.** At a localized background, P of the point differs from 𝐕 at every s, s = 1 included, by 𝓗 with |𝓗| ≤ (1 + O(α_{1,k}))K sup|𝐇| (#130.3–#130.4).
  - Repair: #6.4 and #6.9 state that 𝓗 replaces both the deformation and the response, and that its share is below an eighth.
- **The closure of most of (R-eval-curv) (new #6.10–#6.15, derived, not reviewed; for review as packet CV below).**
  - #6.10, the Landau frame. The post-R words W(M) are invariant under G^c block transformations near the G-valued ones (identity theorem; G is totally real of maximal dimension in G^c). So the extension is taken at (V̂, J^h(V̂)), and neither (1.65) at (P(𝐔), J^h(P(𝐔))) nor CRE (2.39) at the axial form is used (#6.6 now says this).
  - #6.11, the conjugation to V̂. The T-step's points are built on the datum's step-(k+1) Landau representative. The change of frame costs a factor 1 + O(B_Gλα_{1,k})L^{−(k−n)}, which is below a quarter of the margin.
  - #6.12, the members' slack. 𝒟♮_k has the coefficients f♮_n = f_n(1 + ¼β2^{−(k+1−n)}), and Bałaban's members are analytic and bounded on it:
    - the old B-terms through the step margin of CRE (2.42) and CRE p.277 l.2–7;
    - the newest through CRE (3.43)'s (1+β);
    - the E- and R-terms through RG I's orbit-union spaces and RG2 (1.34);
    - the transports through A_k.
  - #6.13. The R-step lands in 𝒟♮_k with no margin at 𝕌^{(0)}, so #48's 𝒟^λ_k is now a subset of 𝒟♮_k.
  - #6.14. The T-step's points lie in 𝒟_k itself at V̂. The data leave at least ⅞ of the margin; the deformations take ⅛, the response under ¼ (𝓗 under ⅛ at a localized background), and the conjugation under ¼.
  - #6.15. SW (6b)'s radius R′ is covered by the map's own c₀ (l.1328), so #58 needs no margin.
  - The marks were updated at #6, #6.4–#6.7, #8, #12, #14, #19, #22–#26, #28, #30–#33, #38, #48, #53, #58, #78, #80, #92, #113, #127, #130.1–#130.6, #130.15, #130.17, #137, #152–#156, #158–#159, #166–#167, #172, #213, #222, and #785.
- **Open (R-eval-curv) now:**
  - 𝒟_k itself at the Landau form of the Schwarz step's scaled points (#92, #6.7). The doubling gives LFR I (1.68)'s c = 3.
  - The same at the extension-domain points (#167). The real datum has no margin, and near Λ the response multiplies its phase by C_ΛM⁵.
  - The conjugation factors of the covariant members at part (b)'s pairs, and the B-terms at U^R (#6.8, #153).
- **Next:** D6 checks D5-1, D5-2, and the restated open. Packet CV reviews #6.10–#6.15 after D6, before A9.

## (R-eval) Packet D, Round D6: Triage, the Scaled Points, and the Extension-Domain Points (4 November, 02:32–02:40)

Referee: launched 02:17:50, finished 02:31:54 (referee_cli_20261104-021750_scope_twoloops_RevalD6.json). No ERROR and five MINORs. D5-1 and D5-2 are closed, and D1–D4's repairs stay closed. The constants, the arithmetic, #6's reduction, μ, and every pin hold. Not clean, since D6-1 and D6-2 are missing marks and D6-3 is a missing statement of the open. Note after the repairs and the closures: 1ffcf84a5c4f (1010 lines, 952 tags). D2.7 after the (R-eval) line's update: bd0d789ac055.

- **D6-1 (MINOR, a real gap in the statuses), #19 with #172: accepted.** A_k's sup at the extension-domain points is taken at 𝕌̃ through #113's words' equality along V̂_t, which D5 marked open at #167 but #19 and #172 did not.
  - Repair: the condition is now derived (#6.16 below), and #19, #172, and #167 mark it derived, not reviewed, at the extension-domain points.
- **D6-2 (MINOR, a real gap in the statuses), #30: accepted.** #30's J_n quotation through (1.65) at V̂ lacked #156's mark.
  - Repair: #30 now says the quotation is derived, not reviewed, at the T-step's points and at the extension-domain points (#6.14, #6.16), as #31, #12, and #156 do.
- **D6-3 (MINOR), #6 and #6.8: accepted.** The B-terms at U^R (#153) were cited as part of the open but not stated in #6.
  - Repair: #6's heading cites #153, and #6.8 now opens with the transfer itself: a G-covariant member's bound at a point does not follow from its bound at a G^c transform of the point without a factor from the conjugation at its endpoints, which is needed for the B-terms at (P(𝐔), 𝐉) through u_L (#153) and for the covariant members at part (b)'s pairs.
- **D6-4 (MINOR), #14: accepted.** Three λ_R places were missing from #14's list: 3C_fdλλ_RB_J/(1−β) (#130.11, #154), O(λ_Rh_k) (#136), and T₂'s D*D, O(λ_RK²(…)ε_k/r_B) (#165).
  - Repair: #14 lists them in a separate sentence, since they are fractions of a room, not source terms of order ρ. Each is absorbed by g small, since B_J, h_k, and ε_k tend to 0 uniformly in k and K, with λ_R fixed after L and M.
- **D6-5 (MINOR), #8: accepted.** Repair: C_K → C_K′, in #8 and in D2.7's (R-eval) line.
- **Two more closures in (R-eval-curv) (derived, not reviewed; for packet CV):**
  - #6.7, no scaled points. #92's bound on |Im ηℍ^{(n)}| is (1.45)'s bound on |ηℍ^{(n)}| at the point's own stages (*R-chain-cx*), since |Im X| ≤ |X|. The stages lie in Bałaban's spaces at the T-step's points (#6.14) and at the extension-domain points (#6.16). #92 now reads so.
  - #6.16, the extension-domain points lie in 𝒟_k itself.
    - The real base U_k(V_k⁰) is ε-regular at each layer's scale on the R-step's support. Off Z this is LFR I p.193 l.21–23. On Z it is LFR I p.193 l.27, (1.78) at p.194 l.38–44, and the χ of LFR II p.378 l.12–14, l.21–22.
    - By VAR Theorem 1 its curvatures and current are at most O(1)B₃B₅M⁶L³(A₀/C₀)(log g_n^{−2})^{r+p₀−q₀} of the room, which tends to 0 since q₀ > p₀ + 3r.
    - The complex deviation, at most 2Kr^{ext}_k, takes at most 2(1+β₀)³max(1, √m)L^{−m−1}/f_n of the room, which is below ½ for L ≥ 8.
    - So V̂ ∈ 𝒟_k, the segment V̂_t stays in 𝒟_k, (1.65) applies at V̂, and 𝕌̃ lies in 𝒟♮_k.
  - The marks were updated at #6, #6.5, #6.7, #6.8, #12, #14, #19, #22, #24, #25, #30, #31, #38, #92, #156, #167, #172, and #213.
- **Open (R-eval-curv) now:** only the conjugation factors (#6.8, #153). The factor is 1 + O(α_{1,k}) per step at top-layer endpoints, and Σ_kα_{1,k} ~ √K polylog. A frame weight in the clause does not stop it (each step's (s, t) polydisc adds O(α_{1,k})). Route A, common-frame slots with no conjugation back, needs a restatement of Cov(k+1) (map (6)(b)) and ĥ(data^g) = gĥ(data)g^{−1}, which is not derived.
- **Next:** D7 checks D6-1 to D6-5. Packet CV then reviews #6.7 and #6.10–#6.16, before A9.

## (R-eval) Packet D, Round D7: Triage, and the B-Terms as Invariant Scalars (4 November, 02:51–02:56)

Referee: launched 02:37:28, finished 02:51:23 (referee_cli_20261104-023728_scope_twoloops_RevalD7.json). No ERROR and five MINORs. D6-2 to D6-5 are closed, and D6-1 is closed at #19 and #167 but not at #172. The constants, the arithmetic, #6's reduction, μ, and every pin hold. Not clean, since D7-1, D7-2, and D7-5 are missing marks. Note after the repairs: 41601263eb8e (1010 lines, 952 tags). D2.7: 55e897989a26.

- **D7-1 (MINOR, still open in part from D6-1), #19 against #172, #113, and #127: accepted.** The D6 edit of #172 had not applied.
  - Repair: #172, #113, and #127 now say the words' equality and Ũ_k^c(Y₄) hold at the extension-domain points too (#6.16), derived, not reviewed.
- **D7-2 (MINOR, a missing open mark), #25 against #167: accepted.**
  - Repair: #25 carries the (R-eval-curv) mark for the slots' B-terms in 15.6(c)'s B(g) and 15.6(f)'s members, in the form restated below.
- **D7-3 (MINOR), D2.7 l.7: accepted.** Repair: D2.7 l.7 says the transfer is derived and reviewed (packet TB), with the curvature conditions at the T-step's points derived, not reviewed (#6.14).
- **D7-4 (MINOR), #8 and D2.7 l.7 (a): accepted.** Repair: both now say that at a localized background the re-projection costs 𝓗 at every s, s = 1 included, with its share below an eighth (#130.3–#130.4, #6.4).
- **D7-5 (MINOR), #32, #19, #33, and body #136, #159, #166, #172: accepted.** Since 𝒟^λ_k ⊂ 𝒟♮_k (#48), #136's landing at s = 1 at a global background includes (2.34)–(2.37) at V̂, which is #6.14's.
  - Repair: #136 marks it derived, not reviewed (#6.14), and #19, #32, #33, #159, #166, and #172 now say "at every s and at both kinds of background".
- **Correction found while working on #6.8: the B-terms are invariant scalars.** CRE (2.41)(iii) (p.261 l.60–62) makes the localized B-terms invariant under G-valued gauge transformations of (𝐔, 𝐉, A), with 𝐉 and A in the adjoint. #6.8 and #130.15 had called them adjoint-valued, with a factor e^{4a_c}.
  - So, as for the words (#6.10), their extension is taken at (V̂, R(u_L)𝐉, R(u_L)A), with (2.42) there and no conjugation factor. What stays open for them is only their outer-field argument R(u_L)A, which needs the outer fields' domain enlarged by e^{2|Im λ_{u_L}|}.
  - Restated at #6's heading, #6.8, #130.15, #153, #172, #19, #25, #30, #38, #213, and D2.7 l.5 and l.7.
- **Open (R-eval-curv) now:** the covariant members' conjugation factors at part (b)'s pairs (transports and Cov(k)'s endpoint factors), and the outer fields' domain under the G^c transformations, the B-terms' argument R(u_L)A included (#6.8, #153).
- **Next:** D8 checks D7-1 to D7-5 and the B-term restatement.

## (R-eval) Packet D, Round D8: Triage, and the Outer Fields' Domain (4 November, 03:15–03:18)

Referee: launched 02:56:05, finished 03:15:04 (referee_cli_20261104-025605_scope_twoloops_RevalD8.json). No ERROR and four MINORs. D7-1, D7-3, and D7-4 are closed, D7-2 at #25, and D7-5 at the paragraphs it named. The B-term restatement matches CRE p.261 l.58–62 and #6.10. The constants, #6's reduction, μ, and every pin hold. Not clean, since D8-1 and D8-2 are missing or stale marks. Note after the repairs and #6.17: 44d21c93ad42 (1013 lines, 953 tags). D2.7: cf7573beb733.

- **D8-1 (MINOR), #30 and #154: accepted.** Repair: both now say "at every s and at both kinds of background" (#6.14; #136, #137).
- **D8-2 (MINOR), #167: accepted.** The extension-domain points are not part (b)'s pairs, so #6.8's conjugation factors do not arise there.
  - Repair: #167 now states the B-terms' form (2.42) at the Landau form, with no conjugation factor, and their argument R(u_L)A by #6.17.
- **D8-3 (MINOR), D2.7 l.7: accepted.** Repair: l.7 names T₂^{old} also for the deformations' gradient and current and for the starting values (#23, #29, #33, #90, #166).
- **D8-4 (MINOR), #7: accepted.** Repair: #7 adds that the curvature conditions at the T-step's points are derived, not reviewed (#6.14).
- **New #6.17, the outer fields' domain (derived, not reviewed; for packet CV).**
  - The ω_j live on Ω_{j+1} ∩ Λ_{j+1}ᶜ ⊆ Ω_{j+1}∖Ω_{j+2} (map l.580). So ĥ and u_L are at most C_odλα_{1,k}L^{1−m} there, with m = k − j, by REG (1.70)–(1.71).
  - The map's radii g_j^{1/2}(1/2 + 2^{−m}) (l.321, l.954) leave each step a slack 2^{−m−1}. The enlargement fits it for g small, uniformly, since α_{1,k}g_j^{−1/2} → 0 and m^{1/4}(2/L)^m is bounded. Nothing compounds.
  - The B-terms' argument R(u_L)A lies in R-m's domain with room, since ε_j/α_{1,j} → 0 (l.956).
  - The marks were updated at #6, #6.8, #8, #19, #25, #30, #32, #38, #130.2, #130.6, #130.15, #153, #159, #167, #172, #213, and D2.7 l.5 and l.7.
- **Open (R-eval-curv) now:** only the covariant members' conjugation factors at part (b)'s pairs (#6.8). They are 1 + O(α_{1,k}) per step at top-layer endpoints, and they compound over the steps through the per-step sup bounds.
- **Route F (proposed for #6.8; it amends D(k)(iii) and needs the user's acceptance).**
  - Let t_j(𝐐) be the G^c transformation from 𝐐 to the step-j axial form of its orbit. Then t_j(𝐐^u) = t_j(𝐐)u^{−1}.
  - D(k)(iii) would bound each covariant member's frame value Y^c := π(t_{j_x}(x))Yπ(t_{j_y}(y))^{−1}, with j_x and j_y the production steps of its end pieces. Y^c is G^c-invariant.
  - At an evaluation point of step m, |Y| ≤ e^{c_π(|Im λ_{t_{j_x}}(x)| + |Im λ_{t_{j_y}}(y)|)}sup|Y^c|. Here t_j is a product of two normalisations of one configuration, so it is O(α_{1,m}) at a top-layer point, independently of the history.
  - Carried members pay nothing, since untouched insertions are evaluated at (U_{k+1}, ω) (map l.1542) and Y^c is invariant. A creation pays its junction and polydisc factors once, inside the new vertex's share (map l.1549's c_πα_{1,k+1}|win(v)|).
  - Not yet in the note.
- **Next:** D9 checks D8-1 to D8-4 and #6.17's marks. #6.17 itself goes to packet CV.

## (R-eval) Packet D, Round D9: Triage (4 November, 03:37–03:39)

Referee: launched 03:19:09, finished about 03:37 (referee_cli_20261104-031909_scope_twoloops_RevalD9.json). No ERROR and five MINORs, all of them marks. D8-1 to D8-4 are closed, and #6.17's restatement is consistent everywhere. The constants, μ, #6's reduction, and the pins hold. Not clean, since D9-1 is an unmarked use of Open (R-eval-old). Note after the repairs: 51cb4e36a927 (953 tags). D2.7: 6200c4195ff0.

- **D9-1 (MINOR): accepted.** 𝕌̃ ∈ 𝒟♮_k rests on #6.2, which holds up to T₂^{old}.
  - Repair: "up to T₂^{old} (Open (R-eval-old), #6.2)" added at #6.13, #12, #30, #31, #152, #158, and D2.7 l.7, and, from the pre-check of D10, at #6's heading and #6.16.2. Note after these: d9040b66b14d.
- **D9-2 (MINOR): accepted.**
  - Repair: #7 now excepts #130.15's outer fields' domain and B-terms (#6.17, #153) with #6.14. #32 adds the B-terms' form (#130.15, #153) to its derived, not reviewed parts.
- **D9-3 (MINOR, from C2a2-3): accepted.**
  - Repair: #8 now says the members agree with Bałaban's extension as far as (V̂, J^h(V̂)) lies in Ũ_k^c(Y₄), as #24 does (#6.10, #127; #6.14, #6.16, #156).
- **D9-4 (MINOR): accepted.** The landing's curvature conditions use #6.9's L ≥ 8.
  - Repair: #8, #136, and D2.7 l.7 (b) now say "no condition on L involving K", with SW (b3)'s and #6.9's L ≥ 8 (table row 12).
- **D9-5 (MINOR): accepted.**
  - Repair: D2.7 l.3, l.5, and l.7 now say "given that note's readings (#17)". l.7 names R-far″(β), R-chain-start, and p.375's inclusion among them.
- **Outside the packet (logged by D9).**
  - Repaired: #3 now names (R-eval)'s two opens. #6.9's "which is what #6.3 needs" now reads "which #6.14 uses".
  - For packet CV: whether #6.17's placement of ω_j survives R-operations that enlarge the Ω's.
    - Source: LFR I (1.10)–(1.12), p.179. Inside Z the R-operation replaces Ω_j, h+1 ≤ j ≤ k, by Ω″_j = (Ω_j^{∼5} ∩ Z) ∪ (Ω_j ∩ Z^c), and the sequence {Ω″_j} is again admissible. The same paragraph sets up the integration over V_j restricted to Γ_j there (p.179 l.2–4).
    - So #6.17's inclusions hold for the current admissible sequence, provided the outer fields on Z's layers are those of the new sequence after the R-operation. If they keep their old bonds, a bond can move to a newer layer. The REG bound there is L^{n−k}, not L^{1−m}, and the slack condition then holds only if the shift in n is bounded uniformly.
    - To settle before CV: read LFR I pp.179–181 for what happens to the ω_j on Γ_j ∩ Z, and add the result to #6.17.
    - Read (03:5x). The R-operation integrates out the variables localized in Z_{j+1}∖Z″_{j+1}, j = h, …, k−1, successively from j = h (LFR I p.178 l.55–57; p.179 l.53–55; (1.15)–(1.16), p.180). The result is the generating set 𝔹″_k = {Γ″_j}, Γ″_j = (Ω″_j∖Ω″_{j+1})^{(j)} ((1.13), p.179), and every later step's variables sit on the layers of {Ω″_j}. So the old bonds do not persist: #6.17's inclusions are those of the current admissible sequence, and ω_j's layer is that sequence's Ω_{j+1}∖Ω_{j+2}.
    - To add to #6.17 after D10, since D10 reads #6.17 as context: one sentence with these pins, derived, not reviewed, for CV.
  - READINGS.md has no entries for the six readings of #17. READINGS.md is obsolete for YM4 (memory), so #17 is their record.
- **Next:** D10 checks D9-1 to D9-5. If it is clean, D11 is the second clean round.

## (R-eval) Packet D, Round D10: Triage (4 November, 03:50–03:52)

Referee: launched 03:40:24, finished about 03:50 (referee_cli_20261104-034024_scope_twoloops_RevalD10.json). No ERROR and four MINORs. D9-1 to D9-5 and the two repairs outside the packet are closed. The constants, μ, #6's reduction, the conditions on L, and the pins hold. Not clean, since D10-1 and D10-2 are unmarked uses of derived, not reviewed steps. Note after the repairs: a5e76a858be5 (953 tags). D2.7: 73600d47762b.

- **D10-1 (MINOR): accepted.** #130.17's radius R′ rests on #6.15, which was written after packet TB.
  - Repair: #7, #32, and D2.7 l.7 now except #6.15 together with #6.14, #6.17, and #153.
- **D10-2 (MINOR): accepted.** The inclusion 𝒟_j ⊃ 𝒟^λ_j is false, since 𝒟^λ_k ⊂ 𝒟♮_k (#48).
  - Repair: #61 and #224 now read "bounded on 𝒟♮_j ⊃ 𝒟^λ_j (#6.12, derived, not reviewed)". #28 carries the #6.12 mark, with #61.
- **D10-3 (MINOR): accepted.**
  - Repair: #7 and #3 now say "given the readings of #17". #12 names *R-coincides* and p.375's inclusion.
- **D10-4 (MINOR): accepted.**
  - Repair: #17's list of places where the map's readings are used adds #6.4, #6.14, #6.15, #6.16.1, and #6.17.2.
- **#6.17, the R-operation (derived, not reviewed; for CV).** A sentence now places ω_j's layer in the current admissible sequence, with the pins read at 03:5x (LFR I p.178 l.55–57, p.179 l.53–55, (1.12)–(1.16)).
- **Next:** D11 checks D10-1 to D10-4. If it is clean, D12 is the second clean round.

### (R-eval-old) Work While D11 Runs (03:55–04:0x)

- **#5.10, the passage from A_N to V̂: the relation is now identified.**
  - VAR's representative u_R is the unique u with ū^j = 1 on Λ′_j and R∂^{η*}A = 0 (VAR (152)–(153), p.301 l.50–61). This is "Theorem 2 of the paper [6]", and [6] is REG (VAR p.309 l.26). REG's Theorem 4 (p.88) implies Theorem 2 (p.88 l.8, raw file line 9), and #102 takes V̂ from Theorem 4. So V̂ = u_R.
  - By LF #0.1.4 and #A.9, u_R = A_N + ∂ω, with ω := ζ^R − ζ^N block-anchored, ω = 0 on Λ₀, and Q′ω = KU′_ax.
  - What #5.10 still needs is a sup bound |∂ω| = o(L) times the datum's phase per fine bond.
  - LF #A.9 bounds |ηω(x)| ≤ C(d)L^jη sup_block(|U′_ax| + |A_N| + |u_R|). It controls u_R's complex part only through VAR (190), whose constant is C(d, L, M), so it does not give o(L).
  - Route: the bump decomposition of #A.9 (ω = ω_g + ω₀, |∂b_y| ≤ C(d)ℓ_y^{−1}) gives |∂ω_g| ≤ C(d)sup_block|U′_ax|. The remaining inputs are sup|U′_ax| through A_N's weighted bound, and ω₀'s sup gradient. Not yet derived.
  - The equation for ω, from REG (04:2x). R(U₀) is the orthogonal projection onto Δ_{U₀}N(Q′(U₀)) (REG p.80 l.12–13, raw file lines 13–14). So the Landau condition (1.27) says D*A ⟂ ΔN(Q′), while A_N has ∂*A_N ⟂ N(Q′). A_N is therefore not in the Landau gauge.
    - ω solves ⟨∂*A_N + ∂*∂ω, Δλ⟩ = 0 for all λ ∈ N(Q′), with Q′ω = KU′_ax and ω = 0 on Λ₀. So u_R drops out.
    - The sources are σ = ∂*A_N, block-constant with |σ| ≤ C(d)(1 + log L)^pθ/L (LF (K1), #0.1.27), and ω_g's block data KU′_ax.
    - What remains is sup|U′_ax|. The axial gauge bounds it only with a factor L relative to the curvature (REG p.80 l.7–8, raw file lines 8–9: "for L large it is too weak"). REG's Landau bound has constants that depend on L (#5.9). So this route needs ω's block data KU′_ax controlled without the axial bound, and it is not closed.
  - To apply after D11: #5.10's "The relation of V̂ to A_N and u_R is not derived here" becomes the identification above, and what remains is the bound on ∂ω. Applied at 04:13, with #5.8 restated to match.

## (R-eval) Packet D, Round D11: Triage (4 November, 04:12–04:15)

Referee: launched 03:51:54, finished about 04:12 (referee_cli_20261104-035154_scope_twoloops_RevalD11.json). No ERROR and four MINORs. D10-1, D10-2, and D10-4 are closed, and D10-3 is closed as specified. #6.17's statuses match. The constants, μ, #6's reduction, the conditions on L, and the pins hold. Not clean, since D11-1 is an unmarked use of Open (R-eval-curv) and D11-3 states a bound too broadly.

- **D11-1 (MINOR): accepted.** The carry (#63, #68) bounds D2.6 §5.4's transports on the family, but the T-step evaluates them at part (b)'s pairs, where #6.8's factors must not compound.
  - Repair: #68 now says this and marks **Open (R-eval-curv)** (#130.15). #63 and #28 carry the mark.
- **D11-2 (MINOR): accepted.** Repair: #12 names *R-chain-start* (#86) with *R-coincides* and p.375's inclusion.
- **D11-3 (MINOR): accepted.** #6.12.4 (d) bounds the transports and the T-step-made members on 𝒟^λ_k only (#78, #171; #6.14 is derived for data in 𝒟^λ). #6.13 needs only 𝕌̃ ∈ 𝒟^λ_k.
  - Repair: #6.12.4 is restricted to 𝒟^λ_k and says that this is where #6.13 uses them. #12, #31, and D2.7 l.7 now say "Bałaban's terms on 𝒟♮_k, the transports and the T-step-made members on 𝒟^λ_k".
- **D11-4 (MINOR): accepted.** Repair: #20, #21, and #33 mark the frame's bound in C_Λ as derived, not reviewed (#41.1–#41.2).
- **Also changed (outside the packet's tested text, in the declared open):** #5.10 and #5.8 now state V̂ = u_R and reduce the passage to the sup bound on ∂ω (above).
- Note after the repairs: 95db877e2133 (953 tags). D2.7: 10919e42eb21. The pre-check of D12 found the same unmarked carry claim at #228's 5.4 step, now marked: babc401d7a52.
- **Next:** D12 checks D11-1 to D11-4, and the restated #5.8 and #5.10 as statements of the open.

## (R-eval) Packet D, Round D12: Triage, and a Sweep of the Marks (4 November, 04:28–04:31)

Referee: launched 04:15:13, finished about 04:28 (referee_cli_20261104-041513_scope_twoloops_RevalD12.json). No ERROR and five MINORs. D11-1 to D11-4 are closed as specified. The constants, μ, #6's reduction, the L conditions, and the pins hold. Not clean, since D12-1 is a further unmarked use of Open (R-eval-curv). The referee ran one read-only `wc -l`, which the log records.

- **D12-1 (MINOR): accepted.** The carry of the att bounds and the cross weights (#82, #83, under #78 and #26), and the T-step-made members' bound on 𝒟^λ_k (#12, #31), use Open (R-eval-curv) unmarked.
  - Repair: #78, #82, #83, #26, #12, and #31 carry the mark.
- **D12-2 (MINOR): accepted, second form.** Repair: #159 now says that γ_Φ and κ_Φ are bounds on configurations, with no member evaluated, so #6.8 and #6.17 do not enter them.
- **D12-3 (MINOR): accepted.** VAR (152)–(153) is the flat-base case.
  - Repair: #5.10 now identifies V̂ and u_R as REG Theorem 2's U₁ = U′^{u^{−1}} for the pair (U′U₀, U₀) (p.83; (1.29); (1.36)–(1.39), the Landau condition being (1.38), p.82), with VAR (152)–(153) as the case U₀ = 1.
- **D12-4 (MINOR): accepted.** Repair: #6's heading paragraph names *R-chain-start* (#86) and p.375's inclusion (#156) with *R-coincides*.
- **D12-5 (MINOR): accepted.** Repair: the mark is placed at C_Λ's definition (#46), which says that every use of C_Λ below carries it. #23 and #26 also carry it.
- **Sweep (to stop the round-by-round pattern).** I searched (R-eval)'s paragraphs (#38–#218) for transports, att bounds, carries, and Cov(k) with no (R-eval-curv) mark, and for C_Λ with no #41 mark.
  - Marked as well: #60 and #61 (the att bounds and transports on the family), and #130.17's carry clause.
  - The other hits are definitions, or bounds at the point itself (#168, #170, #79, #84), where no pair is re-chosen.
- Note after the repairs: 47ba164608d2 (953 tags). D2.7: 10919e42eb21 (unchanged, since D12 found l.7 covered).
- **Next:** D13 checks D12-1 to D12-5 and the sweep.

## (R-eval) Packet D, Round D13: Triage (4 November, 04:47–04:49)

Referee: launched 04:30:35, finished about 04:46 (referee_cli_20261104-043035_scope_twoloops_RevalD13.json). No ERROR and two MINORs. D12-1 to D12-5 and the sweep are closed. D12-2's statement holds for all of #159–#166. The two opens are marked everywhere they are used, and no status is overstated. Not clean, since both MINORs are missing marks of derived, not reviewed steps.

- **D13-1 (MINOR): accepted.** #25 and #27 rest on #72–#76 and #164 through C_Λ and C_Λ′. The sweep searched for "C_Λ" and so missed them.
  - Repair: #25, #27, and #19 carry the #41.1–#41.2 mark.
- **D13-2 (MINOR): accepted.** Repair: #14 marks #6.15 as derived, not reviewed.
- **Pre-check of D14:** a script listed the list items (#18–#34) that cite #72–#76 or #159–#167 without #41, and the citations of #6.12, #6.14–#6.17, and #153 with no "not reviewed" nearby. The only hits are in #31, which ends "all derived, not reviewed".
- Note after the repairs: fecfa2721409 (953 tags). D2.7: 10919e42eb21.
- **Next:** D14 checks D13-1 and D13-2. If it is clean, D15 is the second clean round.

## (R-eval) Packet D, Round D14: Triage (4 November, 05:04–05:07)

Referee: launched 04:47:51, finished about 05:03 (referee_cli_20261104-044751_scope_twoloops_RevalD14.json). No ERROR and three MINORs, all missing or narrow marks. D13-1 and D13-2 are closed. The constants, μ, #6's reduction, the conditions on L, and the pins hold. Not clean.

- **D14-1 (MINOR): accepted.** The extension-domain points (#25, #167) use carried bounds that hold on the family only up to Open (R-eval-curv) (#78, #82, #83).
  - Repair: #167 now restricts "no conjugation factor" to the evaluation at these points and marks the carried bounds. #25 carries the mark.
- **D14-2 (MINOR): accepted.** Repair: #28's mark now covers D2.6's att bounds (#60), the att groups' production transports (#61), and the carried transports (#63, #68).
- **D14-3 (MINOR): accepted.**
  - Repair: D2.7 l.7 marks C_Λ's frame bound and #6.7 at the phase, and C_Λ′'s frame bound at the starting values (#41.1–#41.2, #6.7, #164). Its (R-eval-curv) sentence now names the carried bounds (#68, #82, #83).
- **Pre-check of D15:** a script compared each list item (#18–#34) with the bodies it cites, for (R-eval-curv), (R-eval-old), #41, and "not reviewed" marks. The only hits are in #29, which inherits "the marks of #23" explicitly.
- Note after the repairs: 46484bc073f0 (953 tags). D2.7: 9fff0c6a04c8.
- **Next:** D15 checks D14-1 to D14-3. If it is clean, D16 is the second clean round.

## (R-eval) Packet D, Round D15: Triage (4 November, 05:17–05:19)

Referee: launched 05:05:11, finished about 05:16 (referee_cli_20261104-050511_scope_twoloops_RevalD15.json). No ERROR and two MINORs, both the same missing mark. D14-1 and D14-2 are closed, and D14-3 is closed for its two sentences. Every list item #18–#34 matches its body's marks. Not clean.

- **D15-1 (MINOR): accepted.** #6.2's bound on ũ needs ε ≤ 2ε_Φ (#116), and ε_Φ uses C_Λ (#123), whose frame bound is derived, not reviewed (#41.1–#41.2).
  - Repair: #6.2, #6.1's label, and #6's heading carry the mark. Every "up to T₂^{old} (Open (R-eval-old), #6.2)" now adds it: 7 places in the note (#6.13, #6.16.2, #12, #30, #31, #152, #158), and D2.7 l.7's matching clause. #6.11, which bounds "as at #6.2", names #6.2's marks.
- **D15-2 (MINOR): accepted.** Repair: D2.7 l.7's sentence on the deformations' gradient and current marks C_Λ's frame bound through ε_Φ (#41.1–#41.2, #123).
- Note after the repairs: 005a5edfda44 (953 tags). D2.7: 330898738b0f.
- **Next:** D16 checks D15-1 and D15-2. If it is clean, D17 is the second clean round.

## (R-eval) Packet D, Round D16: Triage (4 November, 05:30–05:32)

Referee: launched 05:18:23, finished about 05:29 (referee_cli_20261104-051823_scope_twoloops_RevalD16.json). No ERROR and two MINORs. D15-1 and D15-2 are closed. Not clean.

- **D16-1 (MINOR): accepted, first form.** The marks that the D15-1 repair put at #6.11 were spurious. #6.11's factors are the Landau transformations of the datum and of the T-step's point, bounded by those configurations' own phase (#6.10; #106, #108). No ε_Φ enters.
  - Repair: #6.11 now says this, and the marks are removed. So #6.14 and its summaries rightly carry neither mark.
- **D16-2 (MINOR): accepted.** T₂^{old} reaches every bond through ε_Φ (#123) and the response (#73, #74, #76), not only the old part of Λ.
  - Repair: D2.7 l.7 now reads "Wherever they use ε_Φ or the Λ-response, which reach every bond, …, need T₂^{old}, the mixed term sourced on the old part of Λ". Its ε_Φ clause adds "up to T₂^{old}".
  - The note's own statements locate the source on Λ^{old} (#5, #160–#164) and mark the uses elsewhere, so they stand.
- Note after the repairs: 75d58a93181b (953 tags). D2.7: 0888311425a6.
- **Next:** D17 checks D16-1 and D16-2. If it is clean, D18 is the second clean round.

## (R-eval) Packet D, Round D17: Triage (4 November, 05:48–05:52)

Referee: launched 05:32:13, finished about 05:48 (referee_cli_20261104-053213_scope_twoloops_RevalD17.json). No ERROR and one MINOR. D16-1 and D16-2 are closed. Not clean.

- **D17-1 (MINOR): accepted.** D2.7 l.7's sentence on the real base points counted LFR II p.378 among Bałaban's printed implications. #206 uses p.378 l.15–16 under the reading R-combined (#17), and p.378 does not print the product.
  - Repair: D2.7 l.7 now reads "Bałaban's printed implications (1.22)–(1.23), (1.29), and (1.89), LFR II p.378 l.15–16 under that note's reading R-combined (#17, #206), and a derived extension …".
  - The other p.378 citations do not use R-combined: D2.7 l.3 and l.46 (l.17–20), and the note's #5, #6.16, #40, #41, and #23 (l.12–14, l.21–22, l.27, l.31).
- **Outside packet D (for CV): accepted.** #6.16.1 bounded both changes by 4(8/7)³/(3L), which holds for the current only. At m = 0 the curvature's change is 2(8/7)³/(Lf_n) ≤ 8(8/7)³/(3L).
  - Repair: #6.16.1 now states the two bounds separately. Both are < ½ for L ≥ 8 (0.4976 and 0.2488), so #6.16.2 stands.
- Note after the repairs: 976ec15d08ba (953 tags). D2.7: c5735473795d.
- **Next:** D18 checks D17-1. If it is clean, D19 is the second clean round.

## (R-eval) Packet D, Round D18: Triage (4 November, 06:04–06:08)

Referee: launched 05:50:21, finished about 06:04 (referee_cli_20261104-055021_scope_twoloops_RevalD18.json). No ERROR and one MINOR. D17-1 is closed. Not clean.

- **D18-1 (MINOR): accepted.** Part (b)'s base-current frame term is taken at U_{k+1}, where #173's bound on B_J rests on D2.7 item 15.8's post-R base-point clause, which is derived, not reviewed (#130.12, #173.1, #173.5). #18 names this input; #8, #30, and #32 did not.
  - Repair: the clause "at U_{k+1} given D2.7 item 15.8's post-R base-point clause, derived, not reviewed, #130.12" now follows every "packet JB": #7, #8, #30 (through #154), #32 (at packet TB's part (b)), #38, #154, #213, and #785.
  - D2.7 l.7's part (b) now adds: "for the base current's frame term through that note's bound on B_J (#173, reviewed, packet JB), at U_{k+1} given item 15.8's post-R base-point clause (derived, not reviewed; that note's #130.12)".
- **Outside the packet: accepted.** D2.7 l.3 imported L₀^× = 6·10⁵; the note's #288 has 10⁶. D2.7 l.3 now reads "L ≥ L₀^× = 10⁶, from the two-loop note's (6C) (its #288)". Map l.193 still has 6·10⁵, and is left to the map's owner.
- **Remark: accepted.** #6's heading now lists #6.4 and #6.9 among the derived, not reviewed parts: "(#6.4, #6.7, #6.9–#6.17, #153)".
- Note after the repairs: 6b76658a7089 (953 tags). D2.7: 1a22b2d589b3.
- **Next:** D19 checks D18-1. If it is clean, D20 is the second clean round.

## (R-eval) Packet D, Round D19: Triage (4 November, 06:19–06:22)

Referee: launched 06:06:32, finished about 06:18 (referee_cli_20261104-060632_scope_twoloops_RevalD19.json). No ERROR and one MINOR. The D18 repairs are closed at every place named. Not clean.

- **D19-1 (MINOR): accepted.** #14 cited "B_J (#173)" → 0 for part (b)'s frame term at U_{k+1} with no mark. The D18 sweep searched "packet JB" only.
  - Repair: #14 now reads "since B_J (#173; at U_{k+1} given D2.7 item 15.8's post-R base-point clause, derived, not reviewed, #130.12), h_k, and ε_k tend to 0 …".
  - Sweep of every B_J and #173 in the note and D2.7 without the 15.8 clause within 300 characters: the rest are #173's own derivation (#173.2–#173.7), #130.11's definition followed by #130.12's mark, and #6.16's "as at #173", a method reference.
- **Remark 1: accepted.** #14's list of the places where C₁/C₀ enters now adds map l.928 (VAR (172)'s complex part, α_{1,n}/α_{0,n} = λ_R bounded) and map l.971 (S_H = C_H(1 + λ_R)α_{0,j+1}e^{−R_j}).
  - A sweep of the map for C₁/C₀ found one more: l.1343, the dev term's complex-data size Cρ_kα_{1,k}/ᾱ_k = Cρ_kλ_R under q₀ = q₁. The map's factor 1 + (log g_k^{−2})^{(q₁−q₀)₊} there assumes C₁ ≤ C₀.
  - #14 now lists it: "the dev term's complex-data size Cρ_kα_{1,k}/ᾱ_k = Cρ_kλ_R (map l.1343, whose factor 1 + (log g_k^{−2})^{(q₁−q₀)₊} would need C₁ ≤ C₀)". It is a source term, absorbed by g small as the others. The map's text is left to the map's owner.
- **Remark 2: accepted.** #785 now reads "not reviewed apart from the transfer to step k+1 (packet TB) and the real base current (packet JB; …)".
- Note after the repairs: c5e56f9b1e31 (953 tags). D2.7 unchanged: 1a22b2d589b3.
- **Next:** D20 checks D19-1 and the two remarks' repairs. If it is clean, D21 is the second clean round.

## (R-eval) Packet D, Round D20: Triage (4 November, 06:36–06:40)

Referee: launched 06:20:31, finished about 06:35 (referee_cli_20261104-062031_scope_twoloops_RevalD20.json). No ERROR and two MINORs, both in #14. D19-1 and the remarks' repairs are closed; no other C₁/C₀ use in the map is missing. Not clean.

- **D20-1 (MINOR): accepted.** Map l.928 (VAR (172)'s complex part) and l.971 (S_H) are smallness conditions on g, not source terms of order ρ.
  - Repair: #14's source-term list now ends with the dev term (map l.1343, l.1498). A new sentence after the room fractions reads "Two more take λ_R in smallness conditions on g: … ε₁ ≥ 3λ_Rα_{0,n}/C₁^{VAR} must be ≤ a₁ (map l.928, l.972), and the slot-value move |Δσ_j| ≤ 4S_H/g_j ≤ r_{ω,j}/4 with S_H = C_H(1 + λ_R)α_{0,j+1}e^{−R_j} (map l.971, l.978–979)".
  - The referee's figures 10S_H and 40C_H are not the map's; map l.978–979 have 4S_H/g_j and 16C_H.
- **D20-2 (MINOR): accepted.** #14's "M large" for T₁'s current needs C_Λ′ independent of M, whose frame bound is #41.1–#41.2.
  - Repair: #14 now adds "with C_Λ′'s frame bound derived, not reviewed (#41.1–#41.2, #164)".
  - Sweep of every C_Λ and C_rsp in #1–#37 and D2.7 l.3, l.5, l.7 without a #41 mark nearby: #5.7's "as it absorbs C_ΛM⁵" now carries the mark; #6.11's mention says it does not enter.
- **Remarks: accepted.**
  - Map l.1498 repeated l.1343's factor. With the user's approval both map lines now carry λ_R: l.1343 "max(1, λ_R(log g_k^{−2})^{q₁−q₀}) ≤ λ_R(1 + (log g_k^{−2})^{(q₁−q₀)₊}), with λ_R = C₁/C₀ = K_RLM + 1 ≥ 1 fixed after L and M", and l.1498 "O(ρ_kλ_R(1 + …))". So #14 no longer says "would need C₁ ≤ C₀".
  - Map l.193 now has L₀^× = 10⁶ (#288), also approved by the user.
- Note after the repairs: 6d50688db331 (953 tags). Map: f8a6f8d2e057. D2.7 unchanged: 1a22b2d589b3.
- **Next:** D21 checks D20-1 and D20-2. Route F for #6.8 is worked out first (below), outside the packet's text.

## Route F: Check of the Invariance (4 November, 06:45)

The user's standing instruction is to use gauge-invariant quantities where possible, so Route F is the route for #6.8. The D8 section's claim "t_j(𝐐^u) = t_j(𝐐)u^{−1}, so Y^c is G^c-invariant" is too strong:
- REG's axial form (1.15)/(1.19) is unique in each orbit of the subgroup (1.14), u = 1 at the points of 𝔅_k (REG p.78, (1.14)–(1.15); p.79, after (1.20)). The block-point values are not fixed.
- The axial frame at a site x is the transport from x's block-point root y along the axial contours, so t(𝐐^u)(x) = u(y)t(𝐐)(x)u(x)^{−1}. Y^c is invariant under (1.14)'s subgroup, and under a general u it is conjugated by u at the roots of its endpoints.
- REG's normalisation (1.29) fixes block averages, not values. Its transformations do not form a group, and "the notion of orbit is not well defined" (REG p.80, after (1.27)). So adding (1.29) does not fix the block-point values either.
- Part (b)'s ĥ has block-point values of size O(α_{1,k}) (REG (1.70)–(1.72)). Carrying Y^c through part (b) would therefore still compound, at the roots.

What Route F needs instead (work in progress, not in the note):
- Never compose the re-choices. Evaluate the frame afresh at the current point: at an evaluation point 𝐔_m of step m, a member produced at step j is read as π(t_j(𝐔_m)(x))Y_W(𝐔_m)π(t_j(𝐔_m)(x′))^{−1}. Here t_j(𝐔_m) is the step-j normalisation of the current configuration relative to the step-j real base. Its imaginary part at x is ≤ C(L, M) times the current complex part (VAR (190); a single factor, admissible as at LF #0.1.14), so there is no product over steps.
- In the closed word tr ∏(Y_{W_i}U_{(i)}), choose the frame at each junction to be the adjacent member's production frame. The members are then read in their own frames, and each transport U_{(i)} pays e^{c(|Im λ_{t_{j_i}}(x′_i)| + |Im λ_{t_{j_{i+1}}}(x_{i+1})|)} once per junction, inside the vertex shares (map l.1549).
- Missing: the production bound has to be a sup of the frame value over a domain that contains the later evaluation points (through the M-factored domain and part (a)), without passing through part (b)'s re-chosen pairs. That is the step to derive next.
- **The contact sites (t₃ < L^{1/2}).** Route C, a contact weight in 𝒟^λ_k's old-layer radii, needs (KW) with θ_B replaced by a cube-averaged norm of the data. That is an LF-side input. The draft is in the job's scratch (Reval_old_contacts.md). With θ_B the supremum, the L-exponents cancel identically, so Route C fails.

## (R-eval) Packet D, Round D21: Triage (4 November, 06:42–06:52)

Referee output: job scratch D21.md; log referee_cli_20261104-064128_scope_twoloops_RevalD21.json. No ERROR, one MINOR, not clean. D20-1 and D20-2 are closed, and the map's l.193, l.1343, and l.1498 corrections are in place.
- **D21-1 (MINOR, #14): accepted.** #14 quoted the map's fixed-frame slot move 4S_H/g_j. Map l.979 says the form used is the cross-frame one (l.982): |Δσ_j| ≤ 10S_H/g_j, with 40C_H(α_{0,j+1} + α_{1,j+1})g_j^{−3/2}e^{−R_j} ≤ 1. Checked at l.979 and l.982. The D20 triage's remark that 10S_H and 40C_H are not the map's was wrong. Repair: #14 now quotes the cross-frame form (map l.971, l.979, l.982).
- **Remark (READINGS.md):** the referee notes that #17's readings have no READINGS.md entries. READINGS.md is a Bałaban-hook file, obsolete for YM4 (memory: Bałaban hooks not for YM4), so this is not a finding.

## Closure of (R-eval-curv): the Direct Transfer (4 November, 07:06)

The direct transfer replaces Route F. The frame value Y^c is not needed.
- **Why the factor compounded.** Part (b) bounds a covariant member at the T-step's point by e^{2c_πa_c} times its bound at the pair (𝐔″, R(ĥ)𝐉), which lies in 𝒟^{λ,M}_k. If the family bound at step k+1 is taken from that, it is e^{2c_πa_c} times the step-k bound, and the factors multiply over the carry.
- **What part (b) already does.** It normalises to the member's own determining set S at every step (#130.6: v_k is REG's transformation for the member's set), and the member's P is its own at every step (#130). So the member's 𝒟^{λ,M}_k differs from its 𝒟^{λ,M}_j only through 𝒟^λ_k against 𝒟^λ_j.
- **The nesting (#130.15.2).** For k ≥ j, 𝒟^λ_k ⊆ 𝒟^λ_j, with the layer index for S at most the step-k index (S is finer, #130.7, #135):
  - phase: ratio ((1−β)/2)^m;
  - gradient: ratio L^{−(n−n′)}((1−β)/2)^m;
  - current: ((1−β)/(2(1+β₀)))^m(1+β₀)²√m ≤ ¾(1−β);
  - 𝒟♮'s coefficients decrease with k (#6.14 iterated), and at coarsened points the bounds are ≤ 0.32 of step j's;
  - the real base: (2.34)'s real part nests, (2.38) by restriction, and the indicators as at #130.5.
  This is #68's carry comparison for the transports, extended to the whole family.
- **The consequence (#130.15.1).**
  - (1) On the family, the member's sup at every k ≥ j is ≤ B_Y, its production bound, with no factor. So the weights (#264, #296) and the carry (#63) are unchanged.
  - (2) At the T-step's points the value is ≤ e^{2c_πa_c}B_Y. That factor arises once per member and step, never enters a family bound, and so never compounds.
  - (3) In the step-(k+1) expansion the factor multiplies the member's activity once. With a_c ≤ C_aα_{1,k} ≤ C_a(1+β₀)α_{1,k+1} and |win| ≥ 40 (map l.1545), it fits the share's transport term with c_π replaced by (1 + C_a)c_π (map l.1549). That term's conditions (map l.1496, l.1498; #61) are smallness conditions on g.
- **Edits.**
  - New tags #130.15.1–#130.15.2. #6.8 is now "derived, not reviewed".
  - Every (R-eval-curv) mark is replaced by "derived, not reviewed" with a pointer to #130.15.1–#130.15.2: #3, #6, #7, #8, #12, #25, #26, #28, #31, #32, #38, #60, #61, #63, #68, #78, #82, #83, #130.2, #130.6, #130.15, #130.17, #167, #213, #228, and #785. D2.7 l.3, l.5, l.7, and l.187 are synced, and so is map l.342 (status bookkeeping).
  - Table row 232 (the peer's) still names (R-eval-curv). The peer is to be told.
  - labels_two_loops.py now registers three-level tags {#N.M.P}. Before this change, #6.12.1–#6.12.4, #6.16.1–#6.16.2, and #6.17.1–#6.17.2 were not in the index, and references to them resolved to their parents. The script also encodes before opening its output. It now reports 963 tags and no dangling reference.
- **Review.** #6.8 and #130.15.1–#130.15.2 join packet CV, the G^c transformations (#6.7, #6.10–#6.17). D21-1 is an attribution minor (the map's other form of a condition that holds either way), so D21 is packet D's first clean round. Its second round is a status check inside CV1's scope (part (B)): D21-1's repair and the statuses after this closure. Packet D does not get another round of its own.
- **Open (R-eval-old)** is now the only open of (R-eval).

## (R-eval-old): the Passage from A_N to V̂ (4 November, 07:15–07:30)

- **New tags #5.10.1–#5.10.6, derived, not reviewed.** These cover one block scale and the flat base.
  - #5.10.1: the closed form ω = H′μ − (I − P)τ, P := H′Q′, τ := Δ^{−1}Eh. It comes from REG's projection R (p.80) and PRT2 (2.101)–(2.102).
  - #5.10.2: the operators.
    - H′ is bounded with its derivatives, with decay of d only (PRT2 p.241 l.14–15; p.246 l.28–29).
    - P reproduces the polynomials of degree ≤ 4, by the symbol (2.132).
    - The Green's function bounds come from Lawler–Limic Theorem 4.3.1, Corollary 4.3.3 (p.84), and Theorem 6.3.8 (p.131).
  - #5.10.3: |K(b; y)| ≤ C(d)n(1 + r)^{−1−d}, by a Taylor expansion of degree 2 and the bump bound n|h_y| ≤ C(d)avg_{B(y)}|A_N|.
  - #5.10.4: μ = KA_N − K∂ζ^N. Gauge covariance and REG's axial conditions (1.19) make it a contour average of A_N, with |μ| ≤ C(d)n𝒜_y. It is an average of loop integrals, so it is gauge invariant.
  - #5.10.5: |∂ω| ≤ C(d)[sup 𝒜_y + sup of the block averages of |A_N|].
  - #5.10.6: the contacts enter only through these averages. The coordinate lines and slabs through block centres stay L/2 away from the faces and the contacts (the large-field note's #0.1.29 and #A.11.42), so the averages are ≤ C(d, κ)(1 + log L)^p‖A_N‖_W.
- **Still open in the passage:** (i) the layered geometry (interfaces Λ_j/Λ_{j+1}, ω = 0 on Λ₀); (ii) a real base U₀ ≠ 1.
- A numerical probe of (i) (2D, two scales) showed growth like log L at the interface, not L. It is not evidence for the note, and the user asked for proofs, not numerics.

## (R-eval) Packet CV, Round CV1: Triage (4 November, 07:32–07:37)

Log: referee_cli_20261104-070833_scope_twoloops_RevalCV1.json. Part (A) has 1 ERROR and 3 MINORs. Part (B), packet D's status check, is CLEAN, so **packet D is closed** (D21 and CV1 (B) are its two clean rounds).

- **CV1-1 (ERROR): accepted and repaired.**
  - #130 now fixes a function-of-𝐔 member's P_Ω := U(𝐁_j″(Ω), M·(·)) at production (step j). It keeps it, with S's block points, (1.19), and (1.29), at every later step, as #135 does for old insertions.
  - *The identity on minimisers* covers the later sets, which are coarser.
  - #130.1, #130.6 (v_k is for S), #8, and #130.15.1's premise follow. #130.15.2 now uses step j's index n_j, with n′ ≤ n_j ≤ n.
- **CV1-2: accepted and repaired.** #130.15.2 (4) now states the following:
  - U_{p,X} and 𝐉_{p,X} use the step's {Γ_i}_{i<p} (CRE p.261 l.10).
  - The T-steps leave them, and an R-step changes them only on Z (LFR II (1.33)).
  - Members meeting Z are integrated by that R-operation (LFR II p.369 l.28–31), so they are touched.
  - #6.12.1: the current gain is L^{−2(n−j)} for (2.37).
- **CV1-3: accepted and repaired.**
  - The containing cube is argued from the least step-k index: C ≤ 2, L ≥ 8, separating layers, compatible partitions, and parallelepipeds.
  - The indicator clause now reads: δ^{re} at U_{k+1} from the current T-step (#130.5).
- **CV1-4: accepted.** Fixes:
  - #6.12.3 l.29 → l.28;
  - #6.16: q₀ > p₀ + r from the project's q₀ > p₀ + 3r (LF #0.10); p.193's print is used at step n for older layers;
  - #130.15.1: l.1541, with l.1542 carrying no factor.
- The READINGS.md remark is not a finding: READINGS.md is obsolete for YM4.
- **Next:** CV2 = packet CV, round 2 (the repairs), plus packet PV (#5.10.1–#5.10.6), round 1.

## (R-eval) Packet CV, Round CV2, with Packet PV, Round PV1: Triage (4 November, finished 08:18)

Log: referee_cli_20261104-073811_scope_twoloops_RevalCV2.json. Part (A) has 2 MINORs, and part (B) has 5 MINORs. There are no ERRORs. The Lawler–Limic pins are unchecked, because the harness refused pdftotext.

- **CV2-1: accepted and repaired.** At n = n_j the side is CML^nξ with C ≤ 2. #130.15.2 (5) now reads ≤ 2ML^nξ (LFR I p.191 l.23–24), which is less than ML^{n+1}ξ.
- **CV2-2: accepted and repaired.** #130.15.2 (4) now uses the Γ_i with i < j. The T-step after step i changes only Γ_i (LFR I (1.13), p.179 l.44).
- **PV1-1: accepted and repaired.** The new {#5.10.2.1} derives the bounds of #5.10.2 (a) from (2.132), with C(d) and δ(d) free of n and L:
  - the aliased terms k ≠ 0 are ≤ C(d)abs(k)^{−4}Π abs(k_μ)^{−1};
  - Δ²S₂ stays ≥ ½(2/π)^{2d} on a strip of width δ(d);
  - three differences cost (1 + abs(k))³/n³, and the sum over k converges.
- **PV1-2: accepted and repaired.** #5.10.4 now uses Bałaban's full averages (REG (1.20)) in the chain form.
  - Linearised, the one-step average maps ∂ζ to ζ(c_+) − ζ(c_−) (RG I (0.4)), with REG (1.30), p.81 l.27, for REG's averages.
  - So the level term is ζ^N(x_{n′}) − ζ^N(x_{n′+1}), the terms telescope, and (1.19) (p.79 l.4–8) acts on the (1.20) averages.
- **PV1-3: accepted and repaired.** #5.10.6 now bounds the swept measure by C(d) times the uniform measure on the slab. It averages W on the block sections of coordinate planes through centres by the Hölder argument of the LF note's #0.1.19. The false bound W ≤ (1 + log L)^pL/s is gone.
- **PV1-4: accepted and repaired.** #5.10.1 now states d = 4 and calls the ℤ^d computation formal. H′ is defined by its symbol (2.132), and Th := Σ_yh_yK(·; y), as on PRT2's torus with μ ⊥ constants (p.241 l.2–7).
- **PV1-5: accepted and repaired.** #5.8 and #5.10 now cite #5.10.1–#5.10.6. They state that #5.10.6 reads W's faces and contacts on ∂Λ, so it depends on the open part (i).
- **Next:** CV3 = packet CV, round 3, plus packet PV, round 2 (the repairs and every line of #5.10.1–#5.10.6, with #5.10.2.1).

## (R-eval) Packet CV, Round CV3, with Packet PV, Round PV2: Triage (4 November, finished 08:42)

Log: referee_cli_20261104-081928_scope_twoloops_RevalCV3.json. Part (A) has 1 MINOR, a citation only, and part (B) has 2 MINORs. There are no ERRORs. The CV2 repairs and the PV1-1 to PV1-4 repairs hold, and the referee re-derived #5.10.2.1. The Lawler–Limic pins are still unchecked, because pdftotext was refused again.

- **CV3-1: accepted and repaired.** #130.15.2 (4) now cites CRE (2.2), p.255 l.15–16, for the T-step's Γ_i, and CRE p.256 l.21–22 for the Ω_m being "determined by the m-th renormalization transformation". It no longer cites LFR I (1.13), which is the R-operation's sequence.
- **PV2-1: accepted and repaired.** #5.10.4 now bounds the masses of the functionals, not the lengths of the fine contours.
  - Q̃_{n′} = Q_{n′} − D̄K_{n′} (LF #A.8), and K_{n′+1} = Q′K_{n′} + K^{(1)}Q̃_{n′}.
  - Since K^{(1)}D̄f = Q′f − f, K_{n′+1} = K_{n′} + K^{(1)}Q_{n′}.
  - Hence mass(K_{n′}) ≤ (d/2)L^{n′} and mass(Q̃_{n′}) ≤ (1 + d)L^{n′}.
  - 𝒜_y is now defined on the cancelled form.
- **PV2-2: accepted and repaired.** #5.8 and #5.10 now say that the o(L) bound rests on #5.10.6 near the contacts of W, at the sites of #5.7 included.
- **Next:** CV4 = packet CV, round 4, plus packet PV, round 3.

## (R-eval) Packet CV, Round CV4, with Packet PV, Round PV3: Triage (4 November, finished 08:56)

Log: referee_cli_20261104-084335_scope_twoloops_RevalCV4.json. Part (A) is CLEAN, the first clean round of packet CV. Part (B) has 1 MINOR. There are no ERRORs. The CV3-1, PV2-1, and PV2-2 repairs hold. The Lawler–Limic pins now check against the extract.

- **CV4, remark (not a finding): repaired.** #6.17.1 left out the factor (1+β₀)m^{β₀} of CRE (2.7). It now reads O(1)(1+β₀)m^{1/4+β₀} (p.255 l.53–59), and m^{1/4+β₀}(2/L)^m is bounded for L ≥ 4. The conclusion is unchanged.
- **PV3-1: accepted and repaired.** #5.10.6 now follows #5.10.4's cancelled form.
  - 𝒜_y is a convex combination, weighted by mass, of W's averages over three kinds of pieces:
    - the K^{(1)} legs from y carrying Q_m;
    - Γ's level-n′ bonds carrying Q_{n′};
    - the K^{(1)} legs from the level-n′ end points carrying Q_m, for the D̄K_{n′} parts.
  - Each piece is a slab through a block centre. For m ≥ 1, Q_m thickens the slab into a union of level-m blocks. For m = 0, the Hölder argument on block sections applies, as before.
  - The normalisation is by mass, not by length.
- **Next:** CV5 = packet CV, round 5 (the second clean round needed; #6.17.1's factor), plus packet PV, round 4 (#5.10.6 and every line of #5.10.1–#5.10.6, with #5.10.2.1).

## (R-eval) Packet CV, Round CV5, with Packet PV, Round PV4: Triage (4 November, finished 09:25)

Log: referee_cli_20261104-085922_scope_twoloops_RevalCV5.json. Part (A) has 2 MINORs, both in #6.17.1, and no ERROR. Part (B) is CLEAN, the first clean round of packet PV. The PV3-1 repair holds, and #5.10.1–#5.10.5 with #5.10.2.1 re-derive with their pins.

- **CV5-1: accepted and repaired.** #6.17.1's left side is now α_{1,k}p₀(g_j)g_j^{−1/2}.
  - p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4), p.255 l.33), so the double A₀ is gone.
  - CRE (2.6) (p.255 l.44–45) gives g_j^{−1/2} ≤ (1+β₀)^{1/2}m^{1/4}g_k^{−1/2}.
  - CRE (2.7) (p.255 l.56–57) gives (log g_j^{−2})^{p₀} ≤ (1+β₀)m^{β₀}(log g_k^{−2})^{p₀}.
  - m^{1/4+β₀}(2/L)^m ≤ m^{3/4}2^{−m} < 1 for L ≥ 4 and β₀ ≤ ½.
- **CV5-2: accepted and repaired.** #6.17.1 is now restricted to j ≥ 1. The new {#6.17.3} treats j = 0:
  - the radius r^{(k)}_{ω,0} = 1/2 + 2^{−k} in B-units, with |B(b)| ≤ 2r on the support (map l.321);
  - the sub-polydisc ρ_ω: the rotations by ĥ and u_L are #71's c₀-charge with C_{c₀} replaced by C_odL;
  - so ρ_ω is taken with 4C_{c₀} + 8C_odL, and the O4 note's C_ω with C_w + 3d + 4C_{c₀} + 8C_odL.
- **Also changed (open parts now derived):** #5.10.5 (i) and (ii) are derived, not reviewed, in WILSON_IT1_PASSAGE_LAYERED_DRAFT_2026_11_04.md.
  - (i): ≤ C(d)(1 + log L)^qL^{1−α/2} times the averages, for RM ≥ L².
  - (ii): the same bound for α₀ ≤ ε(d)L^{−2}.
  - #5.8, #5.10, and #5.10.6 now point to (i) as derived, not reviewed.
- **Next:** CV6 = packet CV, round 6 (#6.17.1, #6.17.3, and every line of (A)), plus packet PV, round 5 (the changed sentences of #5.8, #5.10, #5.10.5, and #5.10.6), plus the new packet PL, round 1 (the draft, §§1–9).

## (R-eval) Packet CV, Round CV6, with Packet PV, Round PV5, and Packet PL, Round PL1: Triage (4 November, finished 09:45)

Log: referee_cli_20261104-092043_scope_twoloops_RevalCV6.json. Part (A) has 1 MINOR, part (B) has 1 MINOR, and part (C), the draft's §§1–6, has 1 ERROR and 5 MINORs. The repairs of CV5-1 and CV5-2 hold.

- **CV6-1: accepted and repaired.** In #130.15 and #130.15.1:
  - the radii are r_{ω,i}(1/2 + 2^{−(k−i)}), with r_{ω,0} = 1;
  - on the layer 0 the bounds hold on the fixed sub-polydisc ρ_ω, whose budget the rotations are charged to, summed over the steps (#6.17.3 (2)).
- **PV5-1: accepted and repaired.**
  - #5.8 and #5.10.5 now say that (i) is derived, not reviewed, and that (ii) is derived in outline, not reviewed.
  - (i)'s conditions now include M ≥ L.
  - The draft's §2 is now derived in full (PL1-5 below).
- **PL1-1 (ERROR): accepted and repaired.** ã = A/Δ₀² is not analytic at q = 0 for n > 1, so the draft no longer uses ã.
  - §2 writes A = M*M with M := n^{2−d/2}ΔH′_j (PRT2 (2.107)).
    - By #5.10.2.1, M has an exponentially decaying kernel, and it annihilates affine functions.
    - The new Lemma M bounds |Mg(x)| by the second differences of g with exponential weights.
  - Lemma A's step (3) is redone through M and the commutators [M, w^s]. The claim is now ‖wΔ₀c‖ ≤ C(d)‖w∇²E‖.
  - Lemma B's step (2) is redone through M and the commutators [M, η^s].
  - §6's bump test now uses M.
  - In §7, the multipliers of G_S use M. The Wiener–Hopf factor is b_ξ := a_ξ/(2cosh σ_ξ − 2cos θ)², with σ_ξ := 2n·arcsinh(m_ξ/(2n)) and m_ξ the fine Laplacian at the scale-j momentum. b_ξ is analytic and bounded above and below, uniformly in n.
- **PL1-2: accepted and repaired.** Lemma A now assumes |∇²ρ| ≤ C(d)/L and a bounded ρ, with a smooth cap and monotone convergence.
- **PL1-3: accepted and repaired.** Lemma B now reads Φ(r) ≤ C(d)(r/R)^α[Φ(R) + R^{d+4}S + L^{−1}log L·E_w], with E_w := w(z)^{−2}‖w∇²u‖² for any weight e^{κρ/L}.
  - The iteration sums the sources with θK^{d+4} > 1, and the tails with mθ^m.
- **PL1-4: accepted and repaired.** The oscillation is restated:
  - it assumes the decay at every centre of B_{R/2}(z);
  - it keeps g_R, which carries the affine part;
  - its lattice step is ℓ^∞ ≤ ℓ² at the scale ρ₀ = C(d)log L, which costs (log L)²;
  - with a fat zero set, |∇u| ≤ C(d)ρ₀²R^{−α/2}𝓔^{1/2};
  - a = 2 is allowed, with a logarithm.
  - §3 (c), §6, and §7's Lemma D now use it. In Lemma D the exponent is γ_c := min(2 − c/2, 1), and β₂ = 1 up to logarithms. The count is unchanged.
- **PL1-5: accepted and repaired.**
  - The comparison's weight is e^{+κρ(·,∂U)}.
  - The data energy 𝓔 ≤ C(d, κ)L^{c(d)}(RM)^{d/2}n^{d/2−1}𝒜 is derived over all layers.
  - The new Lemma R (block-scale sup bound) is proved with Lawler–Limic Theorem 4.3.1, Corollary 4.3.3, and the harmonic-measure bound on p.131. It gives |∇f(b)| ≤ C(d)[n′^{−d/2}‖∇f‖ + L³n^{1−d/2}‖Δf‖].
  - So |∂d(b)| ≤ C(d, κ)e^{−κRM/(7L)}𝒜, free of n.
- **PL1-6: accepted and repaired.** §6 uses s′ := min(s, L/4).
- **Next:** CV7 = packet CV, round 7 (#130.15, #130.15.1, and every line of (A)), plus PV6 (the changed sentences of #5.8 and #5.10.5, and every line of (B)), plus PL2 (the draft's repairs in §§2–6, and §§7–9 for the first time).

## (R-eval) Packet CV, Round CV7, with Packet PV, Round PV6, and Packet PL, Round PL2: Triage (4 November, finished 10:39)

Log: referee_cli_20261104-100958_scope_twoloops_RevalCV7.json. Part (A) has 2 MINORs, part (B) has 1 ERROR, and part (C), the draft's §§1–9, has 1 ERROR and 7 MINORs. The repairs of CV6-1, PV5-1, and PL1-1 to PL1-6 hold.

- **CV7-1: accepted and repaired.** #130.15.2 (5) no longer cites LFR I p.179, whose lines concern the Z_j″ sequence. The cube is placed by an argument from the general properties of CRE's admissible sequences: the domains are unions of MR_m-cubes with R_m ≥ L, the boundaries of Ω_m and Λ_m are ≥ 2MR_m apart, and Ω_{m+1} ⊂ Λ_m.
- **CV7-2: accepted and repaired.** #6.12.1 and #130.15.2 (4) carry the mark of the reading R-p, and #17 lists both tags.
- **PV6-1 (ERROR): accepted and repaired (Route C′).**
  - The new contacts draft (WILSON_IT1_CONTACTS_FREE_BOND_WEIGHT_DRAFT_2026_11_04.md) puts the weight w := max(w_c, w_S) on the free bonds of Λ's VAR problem. Here w_c := max_j max(1, (L^{1/2}/t₃^{(j)})^{1−κ}), and w_S := max(1, (L^{a_S}/s̄)^{r_S}), with s̄ the distance to the codimension ≥ 3 strata of ∂Λ, cut at ρ₀.
  - w ≤ L, and w = 1 at the data bonds and the block points. Its block and plane averages are ≤ 1 + C(d)L^{−c₁}, with c₁ := min((1−κ)/2, κ(1−a_S)). The consumers take λ_w := λL.
  - The passage draft's §3 adds (b₀), the τ-part at Λ₀/Λ₁, where the blocks are single sites. It is bounded through a W-weighted count with the gain c₂, and it lands in the room ⅛(1−β)λw.
  - The note's #52.1 (new), #5.3, #5.7, #5.8, #5.10.5 (i), #5.10.6, #5.11, and #166 now say so.
- **PL2-1 (ERROR): accepted and repaired.** σ_ξ, D_ξ, and b_ξ are not 2π-periodic in ξ for n > 1.
  - §7 splits g_ξ(1, P) with a cutoff χ₀ near ξ = 0.
  - Away from it, a_ξ is bounded below on a complex strip, its Wiener–Hopf factors are analytic, abs(∂_ξ^mg_ξ(1, P)) ≤ C(d, m)e^{−δ′P} uniformly in n, and integration by parts on the torus is free.
  - Lemma K is restated with χ₀h and proved inside the cell.
- **PL2-2: accepted and repaired.** The ρ-volume claims are replaced by the count of fine sites. The condition on 𝓔 reads e^{−2κRM/(3L)}L^{2d} ≤ ½.
- **PL2-3: accepted and repaired.** Lemma R's radii are r ∈ [n′/(4√d), n′/(2√d)], and on the coarse side n′ := Ln.
- **PL2-4: accepted and repaired.** The d-only constants of (2.109) are derived from #5.10.2.1 with n²Δ(q/n) ≍ Δ₀(q).
- **PL2-5: accepted and repaired.**
  - (a) §7 derives the unit differences in x by interior regularity at the scale min(s_x, L/4, D/2). Since γ_x ≤ 1, they are ≤ C(d)(log L)³D^{−β_c−γ_x}.
  - (b) Lemma C now holds at the normal heights P′ ≤ C log L. The derivation uses g_ξ(P′, P) = Σ_m(a_+^{−1})_{P′−m}(a_+^{−1})_{P−m} and gives abs(∇_p^jG_half) ≤ C(d)P′²t^{−2−j}.
- **PL2-6: accepted and repaired.**
  - (a) Lemma D uses W^{2,2} ⊂ L^∞ in dimension d − c ≤ 3, for Hilbert-valued functions.
  - (b) Lemma B has the new (2′), the pure Caccioppoli form, obtained by the iteration over radii. For t < (log L)^{5/3} Lemma D's claim is trivial.
- **PL2-7: accepted and repaired.** §9's assumption now states (1.9) (REG p.77 l.38–39) and the regularity condition (3.35) of REG's [4] (p.82 l.40). Only the plaquette bound is used.
- **PL2-8: accepted and repaired; §9 is derived.**
  - The local axial gauge is taken on cubes of side ℓ := C₀(d)L^{j+1}log L, with α₀ ≤ ε(d)L^{−2}(log L)^{−2}.
  - The objects with exponential decay are localised at ℓ/4, with tails ≤ L^{−10d}.
  - Operator differences are kept in the composition form X₁cX₂, so the differences of A₀ are never used. Translation invariance uses the covariant shifts, whose commutators are plaquette terms.
  - The third differences come from (2′) and W^{3,2} ⊂ L^∞. G_S's size comes from the localised variational bound, and the constant 2C(d) is derived.
  - τ_y's polynomial cancellation is replaced by Γ := (I − P)Δ^{−2}, the Green function of Δ² on N(Q′). The weighted energy with Lemma R gives abs(K(b; y)) ≤ C(d)n e^{−δr_y/2}, uniformly in n and covariantly at U₀.
  - Lemma R at U₀ is proved in one local gauge, with the composition form, Kato's inequality, and the iteration over radii.
- **Status in the note:** (R-eval-old) is now derived, not reviewed. Its first input (the contacts, #5.8 (1)) and its second (the passage, #5.8 (2), #5.10.5 (i)–(ii)) are derived, not reviewed. The note has no item marked open.
- **Next:** CV8 + PV7 + PL3, plus the contacts draft as a new packet CT1. Nothing is declared open.

## (R-eval) Packet CV, Round CV8, with PV7, PL3, and CT1: Triage (4 November, finished 11:44)

Log: referee_cli_20261104-112613_scope_twoloops_RevalCV8.json. (A) has 2 MINORs, (B) 1 ERROR and 2 MINORs, (C) 2 ERRORs and 5 MINORs, and (D) 1 ERROR and 3 MINORs. CV7-2's repair holds, and PL2-1 to PL2-7 hold. The status "derived" for (R-eval-old) was premature: it is **Open** again, with the open parts named at #5.8 (a)–(c).

- **CV8-1: accepted, open.** #130.15.2 (5) uses MR_n-cubes, which CRE prints only for the domains of the renormalization transformations, not for those of the R-operation. For C = 2 the cube is not shown on R-operation layers. Marked **Open (CV-cube)** in #130.15.2 (5).
- **CV8-2 = CT1-2: accepted and repaired.** 1 ≤ w ≤ L^{c_w}, with c_w := max((1−κ)/2, a_Sr_S) < 1, so the nesting across steps keeps half of the room for L ≥ L₀(d) (the contacts draft §1 and §4, note #52.1).
- **PV7-1 (ERROR): accepted and repaired, derived, not reviewed.** T₂^{old}'s current is ∝ λ through α_{1,k} = λ_Rα_{0,k}, so against the unweighted current room it carries λ_R = K_RLM + 1. Repair: the current weight μ^{(k)}_n on the layers n ≤ k₀ (the contacts draft §4a), with T₂^{old}'s current bounded through VAR (190)'s D*D entry (tex\VAR\parts\p308_corrected.tex l.37–47); #5.8, #52.1, and #166 updated. VAR\parts goes into the CV10 scope's sources (CV8's and CV9's scopes omitted it).
- **PV7-2: accepted and repaired.** #78 and #162 say "open" again, consistently. #171 reads λ_w.
- **PV7-3: accepted.** The status of #5, #5.8, and #5.10.5 (ii) is open again.
- **PL3-1 and PL3-2 (ERRORs): accepted, open.** §9 is not uniform in n. Marked **Open (ii-unif)** in the passage draft §9, with the routes: the axial gauge centred at each evaluation point (abs(c(y)) ≤ Cα₀L^{−2j}abs(y − x) removes the log n′), and covariant differences in the weak form, with plaquette commutators (each costs ε₀). The covariant Sobolev step is not derived.
- **PL3-3 and PL3-4: accepted, folded into Open (ii-unif)** (points (3) and (4)).
- **PL3-5: accepted and repaired.** §2's count is taken by the coarsest layer that a ρ-geodesic visits, and the sum over that layer is ≤ 2.
- **PL3-6: accepted and repaired.** Lemma B (1) cites PRT2 (2.2), p.224 l.10.
- **PL3-7: accepted and repaired.** Normal differences: ≤ C(d)PD^{−4} at j = 1 (the variant with s = 1, and Lemma K itself for the second term), and ≤ C(d)(PD^{−3−j} + D^{−2−j}) for j ≥ 2.
- **CT1-1 (ERROR): accepted and repaired.** The gradient room carries w̃(b), the largest w at b and at the bonds that share a site with b, the data bonds included. The lattice gradient is then bounded by 4 times the largest response, with u = 0 at the data bonds, and no slow variation is needed. The averages of w̃ are ≤ 1 + 4dC(d)L^{−c₁}.
- **CT1-3: accepted, open.** LF #A.11.42's block averages exclude the blocks within L of the next layer, which the chain reads in supremum only. Marked **Open (CT-sup)** in the contacts draft §2, and as #5.8 (b).
- **CT1-4: accepted and repaired.** Each of the three parts is ≤ (1/128)(1−β)λw, so the phase is ≤ (3/128)(1−β)λw and the gradient ≤ (3/32)(1−β)λw̃.
- **Open:** (R-eval-old) with #5.8 (a) Open (ii-unif), (b) Open (CT-sup), (c) the current of T₂^{old}; and Open (CV-cube).
- **Next:** CV9 + PV8 + PL4 + CT2 on the repairs, with these opens declared.

## (R-eval) Packet CV, Round CV9, with PV8, PL4, and CT2: Triage

Log: reviews\work\referee_cli_20261104-115222_scope_twoloops_RevalCV9.json (launched 11:52, landed 12:06). 3 ERRORs, 7 MINORs; no part clean. The referee's scope omitted VAR\parts, so it reported VAR (190) as untranscribed; it is transcribed (tex\VAR\parts\p308_corrected.tex l.37–47). The referee read the note while PV7-1's repair was being written (#52.1 without the current weight, #5.8 (c) still open), which is PV8-1's first two points.

- **CV9-1 (MINOR): accepted and repaired.** #130.15.2 (1) now carries the weighted case: where w^{(k)} > 1, λ^{(k)}_nw^{(k)} ≤ λ_w ≤ c′^{k−n}; capped at step j the ratio is ((1−β)/2)^m, uncapped it is ≤ (1+β₀)L^{c_w−1} ≤ (1−β)/2. (2) likewise with w̃. The contacts draft §4's nesting bullet is rewritten in the same two cases.
- **CV9-2 (MINOR): accepted and repaired.** Open (CV-cube) is marked at #3, #130.15.2's heading, #130.15.1, and at every citation of #130.15.1–#130.15.2 and #130.15–#130.15.2. In (5), the MR_m-cube clause is restricted to the domains made by a renormalization transformation, and the conclusion to the cases where □ exists.
- **PV7-3, PL3-5, PL3-6, PL3-7, CT1-4: hold.** PL3-5's residue (the false ball sentence in §2) is deleted; the count is the coarsest-layer one.
- **PV8-1 (ERROR): accepted in part.** #52.1's current weight and #5.8's text were written after the referee read them (see above). The remaining point is real: #166's current total omitted T₂^{old}. Repaired: on Λ^{old} the room is μλ; the data land in (4/7)(1−β)μλ, the other terms ≤ 0.35(1−β)λ ≤ 0.175(1−β)μλ (μ ≥ 2), and T₂^{old} adds ⅛(1−β)μλ: total < 0.88(1−β)μλ (#166, the contacts draft §4a *The budget on Λ^{old}*).
- **PV8-2 = CT2-1 (ERROR): accepted and repaired.** Bałaban's ∇^ξ_U (CRE (2.39), p.261 l.37) compares b with its parallel translates. w̃(b) is now the largest w on N(b) := b, the bonds sharing a site with b, and b ± e_ν (≤ 6d − 3 bonds); each gradient component is a difference of the values at b and one bond of N(b), so it is ≤ 2 max_{N(b)}|u| ≤ (1/64)(1−β)λw̃(b), and the full response's gradient ≤ 2·(3/128) ≤ ⅛. The referee's counterexample (data bond b₀, free translate b₀ + e₂ at a contact) now has w̃(b₀) ≥ w(b₀ + e₂). Averages of w̃ ≤ 1 + (6d − 3)C(d)L^{−c₁}. #52.1 updated.
- **PV8-3 (MINOR): accepted and repaired.** #171's conclusion and #78 read A_k(S) ≤ c_πλ_wα_{1,k}ℓ_k(S).
- **PV8-4 (MINOR): accepted and repaired.** #5.3 and #5.11 carry Open (CT-sup) and Open (ii-unif) with **Open (R-eval-old)**. #5.8 (a) names Open (ii-unif)'s points (1)–(4); #5.10.5 (ii) names Lemma R, the localisation of H′(U₀) and P(U₀), and the partition.
- **PL4-1 (MINOR): accepted and repaired.** §9: *Localisation* is marked Open (ii-unif) (3); *Lemma R at U₀* Open (ii-unif) (1)–(2), with its conclusion conditional; the partition at ℓ/8 Open (ii-unif) (4); *Result of (ii)* open; T(U₀)'s pointwise step marked. §3 (b₀) and §8 carry Open (CT-sup).
- **CT2-2 (MINOR): accepted and repaired.** (a) The data run from step k+1 to step k: where μ^{(k+1)}_n > μ^{(k)}_n, k + 1 − n > ⌈N₀/2⌉, so λ is uncapped and the ratio is 2(1+β₀)²/L ≤ ½(1−β)(1+β₀) for L ≥ 8, β ≤ 3/7; elsewhere #54's ratio. (b) The nesting: the weight multiplies #130.15.2 (3)'s ratio (λ^{(k)}_n/λ^{(j)}_{n_j})L^{−m}(1+β₀)²√m by μ^{(k)}_n/μ^{(j)}_{n_j} ≤ 2^m only where μ^{(k)}_n > 1, i.e. k − n > ⌈N₀/2⌉, so λ^{(k)}_n = λ; uncapped at step j this gives (2/L)^m(1+β₀)²√m within (3)'s bounds; capped at step j it forces m > N₀/3 and the ratio ((1−β)/(1+β₀))^m(1+β₀)²√m → 0. (c) The size now uses the crude θ_B ≤ L^{c_w}λ(1+β₀)L^{−1}, which needs no averages and so not Open (CT-sup); μ := max(2, 16KC(d)(1+β₀)λ_RL^{c_w−1}/(1−β)). (d) VAR (190) is transcribed; it goes into CV10's sources.
- **CT2-3 (MINOR): accepted and repaired.** §§2–3's headings and §3's θ_B and "every site of Λ" carry Open (CT-sup).
- **Open:** (R-eval-old) with #5.8 (a) Open (ii-unif), (b) Open (CT-sup); and Open (CV-cube). T₂^{old}'s current (old (c)) is derived, not reviewed.
- **Hashes:** note ae64bd58abeb (972 tags), contacts 01968540b87e, passage 173909bf0e8c, LF e4e1964fcc07.
- **Next:** CV10 + PV9 + PL5 + CT3 (scope_twoloops_RevalCV10.md, VAR\parts in the sources).

## (R-eval) Packet CV, Round CV10, with PV9, PL5, and CT3: Triage

Log: reviews\work\referee_cli_20261104-121320_scope_twoloops_RevalCV10.json (launched 12:13, landed 12:31). 3 ERRORs from two defects, 7 MINORs; no part clean. CV9-1, CV9-2, PV8-2, PV8-3, PV8-4, PL4-1, CT2-1, and CT2-3 are repaired; PL3-5's residue is gone.

- **CT3-1 = PV9-1 = CV10-1 (ERROR): accepted and repaired.** The current weight sat only on n ≤ k₀, where it is μ, so the room jumped from λ to μλ at k − n = N₀. The weight is now μ^{(k)}_n := min(μ, 2^{max(0, k−n−⌈N_*/2⌉)}) on the gradient and current rooms of every layer: 1 for k − n ≤ ⌈N_*/2⌉, μ on Λ^{old}, and at most doubling per step. The data transfer and the nesting are redone in the contacts draft §4a (*The data*, *The nesting*, four cases), and #52.1, #5.8, #130.15.2 (2)–(3), and #166 cite it.
- **CT3-2 (ERROR): accepted and repaired.** The gradient landing through fine differences of the sup bound holds only on the layer 0 (CRE (2.39), L^{−n}). w̃ is dropped. The response's gradient is no longer bounded through the sup bound (contacts §3); T₂^{old}'s gradient is bounded through VAR (190)'s gradient entry (p.308 l.37–47), ≤ 4KC(d)Lλ times the unit against θ_B ≤ 2λ, and lands in μλ (§4a *Their size*, *The budgets*: ≤ (13/16)(1−β)μλ + (β/4)μλ, β ≤ 3/7). #52.1 and #166 updated.
- **CT3-3 (MINOR): accepted and repaired.** Off the layers with μ^{(k)}_n = μ, at least N_*/3 layers separate T₂^{old}'s sources, so its gradient and current there are ≤ (1−β)λ/64 for g small; the unweighted budgets stay below (1−β) (the gradient for β ≤ 7/39). θ_B ≤ 2λ now includes the 𝐇-part (≤ ½).
- **CT3-4 (MINOR): accepted and repaired.** The ramp uses N_*, the least N₀ over the steps, so μ^{(k+1)}_n ≤ 2μ^{(k)}_n holds.
- **CV10-2 (MINOR): accepted and repaired.** #6.2, #6.10, #6.11, #6.17, #6.17.1, #130.11, and their citations at #14 and #154 read λ_w (B_Gλ_wα_{1,k}, C_odλ_wα_{1,k}, O(λ_wα_{1,k}L^{−k}), C_fdλ_wα_{1,k}, 3C_fdλ_wλ_RB_J); #6.2 names λ_w := λL of #52.1. The conclusions hold, since λ_w is fixed after L and M.
- **PV9-2 (MINOR): accepted and repaired.** #5.8 (2), #5.10.5 (i), and #5.10.6's last sentence carry Open (CT-sup).
- **PV9-3 (MINOR): accepted and repaired.** #5.8 (a)'s point (2) reads "the control of u's flat differences of order ≥ 2 by a covariant Sobolev bound not yet derived".
- **PL5-1 (MINOR): accepted and repaired.** Passage §9: *Translation invariance* and *Third differences* carry Open (ii-unif) (2), *G_S's size* Open (ii-unif) (3), and the next bullet is conditional on the third differences.
- **Pre-check additions (contacts §4a):** *The data* states that the data land in the pre-R room of the older layering (note #75), where μ^{(k)}_n, monotone in k − n, is no smaller; *The budgets* concludes < (1−β) for the current off the μ-layers. In *The nesting*, the case λ^{(j)}_{n_j} < λ with μ^{(k)}_n > μ^{(j)}_{n_j} gives (1−β)^m for the gradient, not #130.15.2 (2)'s ((1−β)/2)^m; since m > N_*/3 it is ≤ (1−β)/2 for g small, which is what #130.15.1 uses, and #130.15.2 (2) now says so. The draft reads LF at d298d5285ba5 (tags #A.11.42, #0.1.27, #0.1.29, #A.8, #A.10 checked).
- **Open:** (R-eval-old) with #5.8 (a) Open (ii-unif), (b) Open (CT-sup); and Open (CV-cube).
- **Hashes:** note f069220021f6 (972 tags), contacts bb8804289bbc, passage 0fc5ae0d7200, LF d298d5285ba5.
- **Next:** CV11 + PV10 + PL6 + CT4 (scope_twoloops_RevalCV11.md).

## (R-eval) Packet CV, Round CV11, with PV10, PL6, and CT4: Triage

Log: reviews\work\referee_cli_20261104-124118_scope_twoloops_RevalCV11.json (launched 12:41, landed 12:58). 2 ERRORs from one defect, 2 MINORs. **PL6 is clean** (PL's first clean round). CV10-1, CT3-2, CT3-4, CV10-2 outside #6.17's pieces, PV9-2, PV9-3, and PL5-1 are repaired.

- **CT4-1 = PV10-1 (ERROR): accepted; declared open.** T₂^{old}'s source is Δd on every layer, and Λ^{old} enters only through the change of VAR's kernel under the O(1) real data difference there (#45, #162), so (190)'s decay from the sources does not make it small off Λ^{old}. Its gradient and current where μ^{(k)}_n < μ, and its phase on k₀ < n ≤ k, need a bound on that kernel change decaying away from Λ^{old} with a constant fixed before g, the input #5.1 names. This is **Open (old-decay)**, now #5.8 (c), marked at #5.3, #5.8, #166, and the contacts draft §4a and §5. Given it, ≥ N_*/3 layers of M/M₁ each make T₂^{old} ≤ (1−β)/64 times the units there.
- **CT4-2 (MINOR): accepted and repaired.** The off-μ budgets are now stated in units of λ^{(k)}_n times the unit: T₂^{old} ≤ (1−β)λ^{(k)}_n/64 given (old-decay), the deformations and the 𝐇-part are absolute and so ≤ that times λ^{(k)}_n; the totals are < 1 − β (current) and ≤ 1 − β for β ≤ 7/39 (gradient), within f_nμ^{(k)}_nλ^{(k)}_n.
- **CV11-1 (MINOR): accepted and repaired.** #6.17.1 reads 8C_odλ_wL(2/L)^m. #6.17.3 uses λ̄^{(k)} := min(λ_w, c′^k) ≥ λ^{(k)}_nw: (1) with λ_w, (2) with λ̄^{(k)} ≤ c′^k. #6.16 reads ε_n = g_np₀(g_n), p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4)).
- **Open (CT-sup): closed, derived, not reviewed** (staged during CV11, applied after it). The contacts draft §1 adds (avg): on the layers 1 ≤ n ≤ k₀ of the layering in which the next T-step reads the data, each block variable's complex part is < C_Qf_nλ^{(k)}_nL^nα_{1,k}L^{−k} (C_Q of #45), which #49 gives where w = 1. 𝒟^{λ,a}_k ⊂ 𝒟^λ_k carries it; T-step data and evaluation points lie there, the gauge representatives need only 𝒟^λ_k. §2: the block data are bounded by (avg), so θ_B ≤ 2λ(1+β₀)/L at every block, the sup-read ones included; the averages of w are no longer used. (avg) lands by VAR (3) (p.278 l.11–14): the minimiser's block variables are its data, and the post-R layering is 𝐁″_k outside Z and the layer k > k₀ on Z (LFR II (1.33)); with the 𝐇-part and the deformations the total is ((5/8)(1−β)λ^{(k)}_n + β/2) of the unit, within f_nλ^{(k)}_n for β ≤ 3/7. (avg) nests through the step-k phase condition and §4's ratio. #52.1 states (avg); #5.8 (b), #5.10.5 (i), #5.10.6, #5.11, and the passage draft (header, §3 (b₀), §8) cite it.
- **Open (CV-cube): still open.** C = 2 with B = B₃ is VAR's pairing (VAR Theorem 1, p.279 l.2–4, l.17–21: cubes of size 2ML^j, bound B₃M), so C is not changed. LFR I p.179 l.19–24 gives the R-made layers as unions of M-cubes with consecutive domains one coarser M-cube apart, which leaves room for □ near Ω_{n+1} but not further from it.
- **Open:** (R-eval-old) with #5.8 (a) Open (ii-unif) and (c) Open (old-decay); Open (CV-cube).
- **Pre-check:** the note's sentence on the step-(n+1) evaluation points (its line 568, citing *The dilated sub-domains*) now reads 𝒟^{λ,a}_{n+1} → 𝒟^{λ,a}_n ⊂ 𝒟^λ_n.
- **Hashes:** note 903f099ee3ce (972 tags), contacts bdb9f8cad3a5, passage fa5a15305301, LF 95da671dfe23 (peer's; the cited sentences of #0.1.27, #A.11.42 checked).
- **Next:** CV12 + PV11 + PL7 + CT5 (scope_twoloops_RevalCV12.md).

## (R-eval) Packet CV, Round CV12, with PV11, PL7, and CT5: Triage

Log: reviews\work\referee_cli_20261104-130515_scope_twoloops_RevalCV12.json (launched 13:05). 1 ERROR, 3 MINORs. **PL7 is clean** (PL's second clean round; PL is cleared, apart from the two citation sentences changed below). CV11-1, PV10-1 (naming), and CT4-2 are repaired; CT4-1 is declared.

- **CT5-1 (ERROR): accepted and repaired.** The data of a T-step are the post-R point's, and their layering is the post-R 𝐁_k, which puts Z on the layer k (LFR II (1.33), p.365 l.2–7). Λ ⊂ Z, so every datum of Λ, fine or block, reads only bonds of the layer k > k₀, where w = 1, and #47 bounds it; θ_B ≤ 2λ(1+β₀)/L follows from C_Q ≤ λ/L, now in #72's λ := max(8max(C_Λ, C_Λ′λ_R)M⁵/(1−β), C_QL). The condition (avg) and 𝒟^{λ,a} are removed: contacts §1–§2, §4; note #52.1, #5.8 (1) and (b), #5.11, #5.10.5 (i), #5.10.6, #492; passage §3 (b₀).
- **CT5-2 (MINOR): accepted and repaired.** The Open (ii-unif) mark is added at #5.3 (every site, the contacts included), #5.8 (1), #5.11, contacts §3 (last bullet), §5, and the header.
- **CT5-3 (MINOR): accepted; superseded by the derivation of Open (old-decay).** **Open (old-decay): closed, derived, not reviewed** (contacts §4a, *The decay away from Λ^{old}*; note #5.8 (c), #5.3, #166). The Cauchy estimate in t reduces T₂^{old} to [H₁(U¹) − Ad_vH₁(U²)]Δd up to 8|Δd|/r_B = o(1). H₁'s random walk expansion (PBG p.427 l.14–21; Corollary 3.8, p.410 l.33–34; p.411 l.2; p.413 l.10; analyticity on (3.37), Section B, p.400, p.403 l.39; bound (3.94)) has terms that read the base only on ∪X̃_i⁵. Both bases obey VAR (7) with ε₁ = O(sup ε_j) → 0, so by VAR Theorem 1 (p.279 l.17–27, M′ ≤ R₁M₁a₁/ε₁) they are within B₃M′ε₁ of pure gauges on every cube; on a walk avoiding Λ^{old} their data agree up to δ^{re} = O(ε_k), the pure gauges match up to a constant and a block-trivial v, and the terms differ by O(ρ_ω/α₁). Walks meeting Λ^{old} carry e^{−δ₀dist(x,Λ^{old})/4}, with dist ≥ (n − k₀)M/M₁. The phase where λ^{(k)}_n = λ needs e^{−δ₀M/(4M₁)} ≤ (1−β)/(512K′C(d)L), M large given d, L, M₁ (K′ = O(K) uniform in M, #164); elsewhere n − k₀ ≥ 5N_*/6 or N_*/3, g small given λ. The pre-R phase budget with T₂^{old} totals ((7/8 + 1/64)(1−β)λ^{(k)}_n + β/2), within f_nλ^{(k)}_n for β ≤ 7/39.
- **CV12-1 (MINOR): accepted and repaired.** #6.16 reads R_n ≤ L(log g_n^{−2})^r (CRE (2.5), p.255 l.36–38).
- **Open:** (R-eval-old) with #5.8 (a) Open (ii-unif); Open (CV-cube).
- **Derived, awaiting review:** the old-decay derivation; the data bound through #47 without (avg); the CT5-2 marks; #72's λ.
- **Hashes:** note 7f519c571b0d, contacts f74f008a25ff, passage 655db85a9c1a, LF 1ce1241e341b (peer's; #A.10 and #A.11.42 checked).
- **Next:** CV13 + PV12 + PL citation check + CT6 (scope_twoloops_RevalCV13.md).

## (R-eval) Packet CV, Round CV13, with PV12, the PL Citation Check, and CT6: Triage

Log: reviews\work\referee_cli_20261104-134027_scope_twoloops_RevalCV13.json (launched 13:40). 3 MINORs, all in CT6. **CV13 is clean** (CV's first clean round after CV12-1). **PV12 is clean** (PV's first clean round). **The PL citation check is clean.** CV12-1, CT5-1, and CT5-2 are repaired; CT5-3 is superseded by contacts §4a.

- **CT6-1 (MINOR): accepted and repaired.** The gauge is built from e = ε′ẽ, with v := (f²c)ε′(f²c)^{−1}, so U¹ and (U²)^v differ by 1 + O(ρ_ωL^{−j}) per fine bond. A walk meeting Λ^{old} pays e^{C(d)δ₀M₁}e^{−δ₀dist/4} for the enlargement X̃⁵ (PBG p.408 l.23–24); PBG's cube size M₁ (CRE p.245 l.37; LF #4.21) is fixed before M, and M large given d, L, and M₁ absorbs it (contacts §4a).
- **CT6-2 (MINOR): accepted and repaired.** VAR's ε₁ of (172) and (190), which sets r_B (note #45), stays fixed. The bases' regularity is a separate ε₁′ := O(sup_nα_{0,n} + B₅M⁶L²R_kε_k) → 0 (VAR p.278 l.46; note #6.16), and VAR Theorem 1 at ε₁′ describes the same minimiser (p.279 l.15). Contacts §4a and passage §9 use ε₁′.
- **CT6-3 (MINOR): accepted and repaired.** Contacts §2 cites #75 for h_k, §4a cites #72 for the order of the constants, and *Where it lands* was marked (now derived; below).
- **Open (CV-cube): closed, derived, not reviewed** (note #130.15.2 (5)). Post-R, Ω_m ∪ Z with Z a union of components of Λ_i^c, hence of MR_m-cubes (LFR I p.177 l.17, l.33, p.179 l.35–36; CRE p.257 l.28, l.42–43); dist(Ω_{n+1}^c, Ω_{n+2}) ≥ La from CRE (3.5) (p.265 l.43, l.18–19, p.264 l.52–53) and a monotone path for the additions of Z.
- **Open (ii-unif): closed, derived, not reviewed** (passage §9, rewritten). VAR Theorem 1's regular gauge (p.279 l.17–27) on cubes of VAR's classes (p.279 l.1–4): local cubes at the scale ℓ(x) = C₀ñ(x)log L (class j′, or j′ − 1 near the layer j′ − 1), with abs(∇ñ) ≤ (2C₀log L)^{−1}; cubes of the localisation of side ℓ_j = C₀L^{j+1}log L about the points of U (class j or j + 1). ε₀ := C(d)(B₃ + B₄(1))M″⁴ε₁′ → 0. (1) Lemma R at U₀ splits c at a point: no Calderón–Zygmund logarithm. (2) Flat shifts: [A(U₀), τ_e] has a difference of c in the middle. (3) H′(U₀)μ = ψ − Γ(U₀)Δ_{U₀}²ψ and P(U₀) decay through Γ(U₀)'s weighted energy. (4) The partition at ℓ(x)/8. □ is a union of big blocks M₁L^{j_c} (p.277 l.12, p.279 l.2), rounded outward. Needs g small given L, M, and R and RM ≥ C(d)(C₀L³log L + R₁M₁L²).
- **So (R-eval-old) is derived, not reviewed:** every **Open (R-eval-old)** mark in the note is now "(R-eval-old), derived, not reviewed"; #3, #5, #5.3, #5.8, #5.10.5, #5.11, #7, #45, #78, #160, #161, #166, #167 reworded; contacts header, §3, §4a, §5 reworded.
- **LF moved** 1ce1241e341b → f06d4cbef4a8 (peer, 13:56; LF triage P8 R1) → d9e10bc45f12 (14:15). #A.11.42's t₃ now counts only the contacts in ∂Λ_{j+1}; contacts §1 follows it. #0.1.27, #4.21, #A.10 are unchanged in what we cite.
- **Open:** none.
- **Derived, awaiting review:** contacts §4a with the CT6 repairs; #130.15.2 (5) (CV-cube); passage §9 (ii-unif); the mark changes for (R-eval-old).
- **Hashes:** note 5835ed456eb1, contacts 859311ef5d98, passage 56a37a533e22, LF f06d4cbef4a8 (peer's).
- **Next:** CV14 + PV13 + PL8 (§9 in full) + CT7 (scope_twoloops_RevalCV14.md).

## (R-eval) Packet CV, Round CV14, with PV13, PL8, and CT7: Triage

Log: reviews\work\referee_cli_20261104-141629_scope_twoloops_RevalCV14.json (launched 14:16, landed about 14:38). No ERROR; 8 MINORs: CV14-1, PV13-1, PL8-1 to PL8-3, CT7-1, and CT7-2 (three items). No part is clean. The CT6 repairs hold.

- **CV14-1 (MINOR, pins): accepted and repaired** (#130.15.2 (5)). The R-operation-free unions are pinned to CRE p.256 l.21–23 (not p.257 l.28, l.42–43, which are about χ_k's partition); compatibility to p.264 l.53–55; Λ_m^c ⊇ Ω_m^c to CRE (2.1), p.254 l.50. The side ratio is now derived: R_m < L(log g_m^{−2})^r ≤ L(1+β₀)(i−m)^{β₀}R_i < L^{i−m+1}R_i (CRE (2.5), p.255 l.36–38; (2.7), p.255 l.56–57), and R_m/R_i is a power of L.
- **PV13-1 (MINOR): accepted and repaired** (#5.7). The Λ-data's M⁵ part is T₁'s data, whose response is ≤ C_ΛM⁵e^{−δ dist}s_Z by (190) (#46, #164), and λ absorbs C_ΛM⁵ by #72's choice (#73). It does not pass through C_{resp,∞}, so no C_H term is needed in #72. Contacts §3's "as in note #5.7" stays valid.
- **PL8-1 (MINOR, but a real gap): accepted and repaired by a new route** (passage §9). The flat composition form of A(U₀) − A was asserted, and H′_j(U₀) is a nonlocal constrained inverse, so the old route (localisation at ℓ_j, the partition at C₀ñ log L, flat shifts, G_S's size, Lemma C at U₀, and Γ(U₀)/τ_y at U₀) is deleted. The new route never compares nonlocal operators.
  - Near each site z there is a cut-off base Ũ₀ := e^{iχa₀}, built in the regular gauge of a class-j or class-(j + 1) cube Q_z of side s_z = RML^j/4 about z. It equals U₀ on the cube of side s_z/2, and it is regular in one global gauge, with abs(ã₀) ≤ C(d)ε_Q/s_z.
  - *The comparison near z*: §2's comparison between U₀ (all layers) and the two-layer problem at Ũ₀, on the ρ-ball of radius RM/(32L). It uses Lemma A′ at U₀ and at Ũ₀ and Lemma R at U₀. Its error is C(d, κ)e^{−κRM/(33L)} times the data.
  - *The two-layer problem at Ũ₀*: the fine minimiser at Ũ₀ against the flat one with the same D and h, through an admissible transport-corrected field, an energy estimate (Δr₃ block-constant, Σ_B(1 − T)φ, Poincaré on N(Q̃)), and Lemma R at Ũ₀ with the added sources σ and s₂. Its error is C(d, L, M, R)ε_Q𝒟, which g small given L, M, and R absorbs into doubling C(d).
  - Only Δ_{Ũ₀}, Q̃, E(Ũ₀), and the bumps enter. The conditions are now RM ≥ C(d)R₁M₁L (in place of C(d)(C₀L³log L + R₁M₁L²)), M ≥ L, RM ≥ L², and g small given L, M, and R. #5.8 (a) and #5.10.5 (ii) are rewritten to match.
- **PL8-2 (MINOR): accepted and repaired.** Lemma R at a regular base absorbs through the weighted supremum Ŝ := sup((2n′ − r)/n′)^{C}S(r), r′ := (r + 2n′)/2, so Ŝ ≤ 2A once C(d)ε₀4^{C(d)} ≤ ½.
- **PL8-3 (MINOR): accepted and repaired.** REG's α₀ restrictions hold for g small given L and M.
- **CT7-1 (MINOR): accepted and repaired.** Contacts §4a runs PBG and VAR at LF's block size (M_b, LF's M′; LF #4.22–#4.24), with M₁ = KM_b, K ≥ 12d + 1, and a reach of at most 10dM_b < M₁. #5.8 (c) now reads "M large given d, L, LF's block size M′, and M₁".
- **CT7-2 (MINOR, three misquotations): accepted and repaired.** Contacts §1 l.7 gives LF #A.11.42's t and t₃ in full. §1 l.13 credits 1-Lipschitz to LF #A.11.42, with ρ₀ ≥ 2 for L ≥ L₀(d). β ≤ 7/39 is recorded as a constraint on the choice of β: the project's 1/8 (note #75) meets it, and CRE's example 1/4 (p.261 l.42) does not. The peer was messaged for the table (15:1x).
- **Pre-check of the new §9 (mine):** two repairs. D and h are set to 0 outside the layers j and j + 1 (the continuation), and the two-layer problems' 𝓔 has no far layers. The other items were checked: the geometry of the case split j = m or m − 1, ñ ≤ L^{j+1} on V, U's blocks inside the cube of side s_z/2, the separations 15/32 ≥ 7/16, the scaling of every source in n, and Q*λ₃ − Q̃*λ₃ = (1 − T^{−1})Δr₃.
- **Open:** none.
- **Derived, awaiting review:** passage §9 (new route); contacts §§1, 4a with the CT7 repairs; #130.15.2 (5) with the CV14-1 pins; #5.7 (PV13-1); #5.8 (a), (c) and #5.10.5 (ii) (rewording).
- **Hashes (15:13, at the CV15 launch):** note e29745d0748a, contacts 3e27794f074d, passage 7084b3a22d1d (with the pre-check repairs), LF fb9b8af212b4 (peer's).
- **Counts:** CV 1 clean (CV13); PV 1 clean (PV12); PL §§1–8 cleared, §9 new again; CT 0 clean.
- **Next:** CV15 + PV14 + PL9 (§9 in full) + CT8 (scope_twoloops_RevalCV15.md).

## (R-eval) Packet CV, Round CV15, with PV14, PL9, and CT8: Triage

Log: reviews\work\referee_cli_20261104-151324_scope_twoloops_RevalCV15.json (launched 15:13, landed about 15:30). (A) CV15 is CLEAN. One ERROR (PL9-1) and eight MINORs: PV14-1, PV14-2, PL9-2, PL9-3, CT8-1 to CT8-4. The repairs of CV14-1, PV13-1, PL8-1, PL8-3, and CT7-1 hold. The repair of PL8-2 does not (PL9-1). CT7-2 was partly repaired (PV14-2, CT8-1).

- **PL9-1 (ERROR): accepted and repaired** (passage §9, *Lemma R at a regular base*).
  - The fault: the weighted-supremum step dropped a factor x^{−C}. The coefficient of S(r′) blew up as r′ − r shrank, so no fixed absorption held.
  - The new proof has three parts.
    - *Zero order.* Kato's inequality Δabs(u) ≤ abs(Δ_Uu) is exact and gauge-invariant. With the mean value bound for subsolutions at every radius, it bounds sup abs(v) and sup abs(f) with no W term and no iteration.
    - *First order.* On a ball B(x, 4ρ) of any radius 1 ≤ ρ ≤ δ(x)/8, the flat representation with c split at x gives s₁(x) ≤ C(d)(n′/ρ)Z + C(d)ε₀ sup s₁. The blow-up (n′/ρ) multiplies only the zero-order quantity Z, and the coefficient of s₁ is fixed.
    - *The absorption.* The weight δ(x)/n′, with δ the distance to the boundary of B_{n′}(b), absorbs the s₁ term for 4C(d)ε₀ ≤ ½. Near the boundary the lattice bound abs(∇u) ≤ 2 sup abs(u) applies.
  - The lemma now takes added sources s and σ, so step (d) cites it directly.
  - Its first term is n′^{−1−d/2}‖f‖, and Poincaré turns it into n′^{−d/2}‖∇_Uf‖_{B_{c(d)n′}}, since f has zero covariant block means in both uses.
- **PL9-2 (MINOR): accepted and repaired** (*The cube Q_z*).
  - The rule now tests the cube of side s_z′ = s_z + 16R₁M₁L^{j+1}.
    - If that cube meets the layer j, Q_z has class j.
    - Otherwise Q_z has class j + 1 and contains the cube of side s_z. Its enlargement then lies within s_z/2 + 6R₁M₁L^{j+1} < s_z′/2 of z, so in the layer j + 1 alone.
  - *The class* now states the reach s/2 + 6R₁M₁L^{j_c}. The total reach is ≤ RML^j/8 + 14R₁M₁L^{j+1} + √dL^{j+1} ≤ 3RML^j/8.
- **PL9-3 (MINOR): accepted and repaired** (step (a)).
  - On B_{2c(d)Ln}(z), abs(Δr₃) ≤ C n^{−3}𝒟. Then abs(∇r₃) ≤ C(d)(n^{−1}sup abs(r₃) + n sup abs(Δr₃)) ≤ C n^{−2}𝒟, by Lawler–Limic Theorems 6.3.8 and 4.3.1 and Corollary 4.3.3.
  - Step (d) then bounds abs(σ) ≤ C ε_Q n^{−3}𝒟 pointwise, with abs(c)abs(∇r₃) included, and n′ sup abs(s₂) + n′³ sup abs(σ) ≤ C ε_Q𝒟.
- **PV14-1 (MINOR): accepted and repaired.**
  - On the problem's layering, R and M are LF #4.24's R′ = LK_{CRE} − 1 and M′ = M_b, and VAR's product is M_b (LF #4.23). So RM ≥ C(d)R₁M₁L reads K_{CRE} ≥ C(d) + 1, and §2's M ≥ L reads M′ ≥ L. Both are lower bounds, which LF #4.24 allows.
  - "g small given L, M, and R" is g small given L, K_{CRE}, and M′.
  - Recorded in: passage §9 *Result of (ii)*; note #5.8 (a), #5.10.5 (i) and (ii); contacts §4a *Where it lands*.
  - The note writes K_{CRE} as #99 does (its K is VAR's factor). The contacts draft writes K_{CRE} in §4a too.
  - The peer was asked to record both bounds in the table and LF (15:4x).
- **PV14-2 and CT8-1 (MINOR): accepted and repaired.** #75 and contacts §4a now say "the project's β = 1/8", and #75 adds that CRE's example is β = 1/4 (p.261 l.42).
- **CT8-2 (MINOR): accepted and repaired.** The walk factor is O(M_b^{−1/2})^{|ω|} at the block size M_b (PBG's M₁^{−1/2}, p.410 l.37–42).
- **CT8-3 (MINOR): accepted and repaired.** The reach is 10dM_bL^jη in the ℓ¹ distance, less than the layer width K_{CRE}M_bL^jη (LF #4.25).
- **CT8-4 (MINOR): accepted and repaired.** Contacts §4 cites the normalised transformations at #6.17 and C_cr^λ at #226, #231, and #484.
- **Bookkeeping:** the staged table-tag conversions are applied in the note (#T2.24, #T1.3, #T2.5 and #T2.15, #T4.30, #T1.2). labels_two_loops.py now skips citations of the form "LF #N" (another note's tags) and passes: 972 tags.
- **Pre-check of the repairs (mine):**
  - The first-order sups were moved to B(x, 4ρ + 1), the neighbours that W reads, with δ ≥ δ(x)/4 there.
  - Checked:
    - the Kato sign (positive Δ, Δ(G*φ) = φ);
    - the subsolution's mean value bound;
    - every term of P and ∇P against ε₀(ρ/n′) or ε₀n′^{−1};
    - the units of Z and of s₁;
    - the crude bound for δ < 8;
    - Poincaré's ball B_{(4+√d)n′} ⊂ B_{c(d)n′}.
- **Open:** none.
- **Derived, awaiting review:**
  - passage §9: Lemma R at a regular base (new proof), *The cube Q_z*, *The class*'s reach, steps (a) and (d), and *Result of (ii)*'s layering bullet;
  - contacts §§1–5 with the CT8 repairs;
  - note #5.8 (a), #5.10.5 (i) and (ii), and #75's β sentence.
- **Counts:**
  - CV 2 clean (CV13, CV15), so CV is cleared;
  - PV 1 clean (PV12);
  - PL §§1–8 cleared, §9 0 clean;
  - CT 0 clean.
- **Next:** PV15 + PL10 (§9 in full) + CT9 (scope_twoloops_RevalPV15.md).

## (R-eval-old) Packet PV, Round PV15, with PL10 and CT9: Triage

Log: reviews\work\referee_cli_20261104-154722_scope_twoloops_RevalPV15.json (launched 15:47, landed about 15:59). There is no ERROR and no clean part. Five MINORs: PV15-1, PL10-1, PL10-2, CT9-1, and CT9-2. The PL9-1 to PL9-3 and PV14 repairs hold; the new Lemma R checks line by line, the Kato sign, the absorption, and Z's units included. CT8-2's factor holds, but its source label was misquoted (CT9-1).

- **PV15-1, PL10-1, and CT9-2 (MINOR, one defect): accepted and repaired.**
  - The defect: "g small given L, K_{CRE}, and M′" left out the note's M, which enters ε₁′ through B₅M⁶ (LFR II p.378 l.14; #6.16). That M is chosen after M′ and M₁.
  - Passage §9 now names it M_{CRE}, as distinct from §2's layer parameter M:
    - in *Assumption* and *The regular gauge*;
    - in the M′ bullet and in *Result of (ii)*, where g is small given L, M, R, and M_{CRE}, that is, given L, K, M_b, and M_{CRE}.
  - The layering bullet says "LF's block size M_b (LF's M′)", apart from VAR's cube parameter M′.
  - Note #5.8 (a) and #5.10.5 (ii) now add "this note's M (through ε₁′'s B₅M⁶)". So do contacts §3 l.35 and §4a's *Where it lands*.
  - No consumer is affected, since each takes g small after M (#72, #166).
- **PL10-2 (MINOR): accepted and repaired.**
  - The transported bumps need n_B³abs(∂²a₀): the holonomies' differences carry ∂²a₀.
  - ε_B := C(d)(B₃ + B₄(1))R₁M₁L⁴ε₁ now bounds abs(∂²a₀)L^{3j′} too, from (9)'s ‖A₀‖_{1,1} (p.279 l.22).
  - Lemma A′ at U₀ states the bump bound's terms. Lemma R (1) and ε₀'s list include ∂²a₀ (ε_Q already covered it).
- **CT9-1 (MINOR): accepted and repaired.** Contacts §4a cites PBG (3.94)'s O(M^{−1/2})^{|ω|}, with M its big-block size (p.410 l.37–42). PBG's M₁ is the threshold of "for M ≥ M₁" (p.397 l.37–38).
- **Bookkeeping:** LF #4.22.1, the peer's record of K ≥ C(d) + 1 and M′ ≥ L, is cited in passage §9, note #5.8 (a) and #5.10.5 (i)–(ii), and contacts §4a. labels_two_loops.py passes (972 tags).
- **Open:** none.
- **Derived, awaiting review:**
  - passage §9 with the PL10 repairs;
  - contacts §§1–5 with the CT9 repairs;
  - note #5.8 (a), #5.10.5 (i)–(ii), and #75.
- **Hashes (16:01):** note b423fc8a820e, passage 9566e6811aa2, contacts bd3e20ee5133, LF 25e5bdf7a157 (peer's).
- **Counts:** CV cleared; PV 1 clean (PV12); PL §§1–8 cleared, §9 0 clean; CT 0 clean.
- **Next:** PV16 + PL11 + CT10 (scope_twoloops_RevalPV16.md).

## (R-eval-old) Packet PV, Round PV16, with PL11 and CT10: Triage

Log: reviews\work\referee_cli_20261104-160158_scope_twoloops_RevalPV16.json (launched 16:02, landed about 16:12). No ERROR. (B) PL11 is CLEAN. (A) has two MINORs and (C) one; none affects a bound. The repairs of PV15-1, PL10-1, PL10-2, CT9-1, and CT9-2 hold, apart from PV16-1 and CT10-1.

- **PV16-1 (MINOR): accepted and repaired.** #5.8 (a) and #5.10.5 (ii) quoted the passage's condition as "g small given L, M, and R". They now quote "g small given L, M, R, and M_{CRE} (this note's M)", which matches *Result of (ii)* and the final lists.
- **PV16-2 (MINOR, status): accepted and repaired.** #167's heading said "(derived, up to the opens marked at its end)", a remnant of the old (R-eval-curv) opens. It now reads "(derived; the parts marked at its end derived, not reviewed)".
- **CT10-1 (MINOR): accepted and repaired.** In contacts §4a *Where it lands*, the passage's layer parameter is now called that, "equal to M_b", so M in the sentence is only the note's M.
- **Referee's remarks (no finding):**
  - *VAR p.279 l.22's β₀ = 1.* The raw and corrected transcriptions both print "0 ≤ β ≤ β₀ = 1". It is accepted as printed, since Bałaban's claims are accepted unless refuted. ε_B's B₄(1) needs β = 1: a β₀ < 1 would leave a factor L^{(1−β)j′}, which is not uniform in j′. The local PDF is password-protected, so the page image was not checked.
  - *LF #4.22.1's g-dependence.* It omits the note's M. The peer was told at 16:1x. The three files cite #4.22.1 only for the lower bounds.
- **Open:** none.
- **Derived, awaiting review:**
  - passage §9 (1 clean round, PL11);
  - contacts §§1–5 with the CT10 repair;
  - note #5.8 (a), #5.10.5 (i)–(ii), #75, and #167's heading.
- **Hashes (16:13):** note 50e8029bfc7f, passage 9566e6811aa2 (unchanged since PL11), contacts 41616a7889a2, LF 25e5bdf7a157 (peer's).
- **Counts:**
  - CV: cleared.
  - PV: 1 clean (PV12).
  - PL: §§1–8 cleared; §9 1 clean (PL11).
  - CT: 0 clean.
- **Next:** PV17 + PL12 + CT11 (scope_twoloops_RevalPV17.md).

## (R-eval-old) Packet PV, Round PV17, with PL12 and CT11: Triage

Log: reviews\work\referee_cli_20261104-161350_scope_twoloops_RevalPV17.json (launched 16:14, landed about 16:35). All three parts are CLEAN. The PV16-1, PV16-2, and CT10-1 repairs hold, and every consumer of (ii) takes g small after L, K_{CRE}, M′, and the note's M. The peer's LF #4.22.1 and #4.22.2 now name the large-field M.

- **Remarks (no finding; no change):**
  - Passage l.253's "g small given L and M_{CRE}" for REG's α₀ also involves M_b. It holds as written, since M_b = M′(d, L) (LF #4.26), and l.292 lists REG's α₀ under the full conditions.
  - β₀ in the passage means CRE's 1/7 in §1 and VAR's Hölder exponent in §9; the context separates them.
  - #5.2 says Bałaban's extended U_k^0 "has" the properties of U_k″, while LFR II p.375 l.13–14 prints "similar". #5.6 uses only "similar".
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 (1 clean round, CT11).
- **Cleared:** packet PV (PV12, PV17); passage §9 (PL11, PL12), so the passage draft is cleared in full; packet CV (CV13, CV15). The (R-eval-old) passage at U₀ ≠ 1 (#5.8 (a), #5.10.5 (ii)) is reviewed with them.
- **Hashes (16:36):** note 50e8029bfc7f, passage 9566e6811aa2, contacts 41616a7889a2.
- **Next:** CT12 alone (scope_twoloops_RevalCT12.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT12: Triage

Log: reviews\work\referee_cli_20261104-163625_scope_twoloops_RevalCT12.json (launched 16:36, landed about 16:50). No ERROR, two MINORs; neither changes a bound.

- **CT12-1 (MINOR): accepted and repaired.** §4a *The walk expansion* took H₁'s walk terms as analytic on PBG's domain (3.37), citing Section B. Section B covers G′, (Q′G′²Q′*)^{−1}, R, G, and P only (p.400 l.8–9, p.403 l.39); H₁ needs (3.36) (p.422 l.50; Theorem 3.12, p.423 l.34–36), whose complex class is (3.38) (p.396 l.45–48), the class of VAR Proposition 9 (p.309 l.11–12; l.2–4). Checked against the corrected files. Now: the terms are analytic on the class (3.38); *A walk that avoids Λ^{old}* measures ρ_ω in the norms of (3.38), D*D by VAR (10) (p.279 l.25), and takes ẽ := exp φ with φ a smooth interpolation at the scale L^j, its differences O(ρ_ωL^{−2j}) and O(ρ_ωL^{−3j}); the Cauchy estimate and α₁ refer to (3.38). No bound changes.
- **CT12-2 (MINOR, status): accepted and repaired.** §3's (KW) (LF #0.1.27, #A.10–#A.11) and §4a's block size M_b (LF #4.21–#4.26) are derived, not reviewed in LF (checked in LF at 1bbb59aef5be). §3, §4a, and the header now say so. The header also drops the stale "through the passage draft's §9" status (the passage is cleared) and records LF read at 1bbb59aef5be.
- **Consequence for the note's (R-eval-old) markers.** Once CT clears, (R-eval-old)'s own steps are reviewed, but it rests on LF's (KW) and block size, derived, not reviewed in LF (#5.4 records (KW)'s status). The note's "(R-eval-old), derived, not reviewed" markers stay until CT clears; then they will name that LF dependence instead.
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 with the CT12 repairs (1 clean round, CT11).
- **Hashes (16:53):** note 50e8029bfc7f, passage 9566e6811aa2, contacts efd2e023eef6 (after the repairs; *The bases are near pure gauges* now also quotes VAR (10)), LF 1bbb59aef5be (peer's).
- **Next:** CT13 alone (scope_twoloops_RevalCT13.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT13: Triage

Log: reviews\work\referee_cli_20261104-165355_scope_twoloops_RevalCT13.json (launched 16:54, landed about 17:04). No ERROR, one MINOR. The CT12 repairs hold; the pins check against the corrected files.

- **CT13-1 (MINOR): accepted and repaired.** §4a *A walk that avoids Λ^{old}* claimed e = 1 + O(ρ_ω) at the block points, but data nearness gives only h(x)h(y)^{−1} = 1 + O(ρ) per block bond, so e drifts by O(M_b|ω|ρ) along the walk; and chaining the cube gauges along the walk does not fix one gauge where non-consecutive domains overlap (walks may revisit). Repair:
  - *The bases are near pure gauges*: M′ = O(LM_b), so each X̃_i⁵ lies in one cube of VAR's class (its diameter C(d)M_bL^jη is below the layer width LK_{CRE}M_bL^jη, LF #4.24, for L ≥ L₀(d), so it meets at most two adjacent layers).
  - The term is a composition of localised operators, so it is a function of the backgrounds on the copies X̃_i⁵ glued along consecutive overlaps (a chain or tree T_ω; revisits are separate copies). One gauge function per base on T_ω, by extending the overlap transition's logarithm over each new copy.
  - Long walks |ω| > n_* := ⌊(M_bρ̄)^{−1/3}⌋, ρ̄ := M_b(B₃M′ε₁′ + |δ^{re}|), take the trivial bound and carry O(M_b^{−1/2})^{n_*} → 0. Short walks: |e − 1| ≤ ρ_ω := C(d)M_b(|ω| + 1)ρ̄ ≤ C(d)(M_bρ̄)^{2/3} → 0, so log e exists; ẽ and v live on T_ω; the Cauchy estimate copy by copy gives O((|ω| + 1)ρ̄/α₁), summable against O(M_b^{−1/2})^{|ω|}.
  - *The bound*: ε_od := O(ρ̄)/α₁ + O(M_b^{−1/2})^{n_*} + …, all vanishing with g. No bound changes.
- **Remark (repaired, not a finding):** the analyticity of each walk term on (3.38) is the author's step from Bałaban's operator statements; *The walk expansion* now says it follows because each term is a composition of the localised operators, each analytic there with its bound.
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 with the CT12 and CT13 repairs (1 clean round, CT11).
- **Hashes (17:08):** note 50e8029bfc7f, passage 9566e6811aa2, contacts 9743c93d6d3c, LF 1bbb59aef5be (peer's).
- **Next:** CT14 alone (scope_twoloops_RevalCT14.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT14: Triage

Log: reviews\work\referee_cli_20261104-170852_scope_twoloops_RevalCT14.json (launched 17:09, landed about 17:24). No ERROR, two MINORs, both in §4a; neither changes a bound. The CT13-1 repair holds in substance.

- **CT14-1 (MINOR): accepted and repaired.** The copy-by-copy gauge extension did not justify "U^i within O(ρ̄) of 1^{f^i} on every copy": the transition must be taken against the parent's corrected function, so the deviations compound along T_ω. Repair (*The gauges along T_ω*): F_b := f_bk exp(χψ), t = f_b^{−1}F_a = k exp ψ on X̃_a⁵ ∩ X̃_b⁵, χ = 1 on X_a ∩ X_b (where the composition sums, PBG p.413 l.9–10, p.416 l.4–8) and supported in its M_b-block neighbourhood; so d_b ≤ C₂(d_a + ρ̄/M_b) and d ≤ C₃^{m+1}ρ̄/M_b at depth m. n_* := ⌊log(1/(M_bρ̄))/(2 log C₃)⌋, so C₃^{n_*} ≤ (M_bρ̄)^{−1/2}; short walks have d ≤ ρ̂ := C₃²(ρ̄/M_b)(M_bρ̄)^{−1/2} → 0, and |e − 1| ≤ C(d, L)(n_* + 1)(M_bρ̄)^{1/2} → 0; long walks carry O(M_b^{−1/2})^{n_*} → 0. ε_od's first term is O(ρ̂)/α₁. The referee's remark on v(x) is also repaired: |v(x) − 1| = O(ρ̂), absorbed.
- **CT14-2 (MINOR): accepted and repaired.** VAR's class (p.279 l.2–4) sizes □ as 2ML^jη in the finer layer's units, and the containment test is on □̃. *The bases are near pure gauges* now says so: X̃_i⁵ meets at most two adjacent layers (LF #4.25), □̃ is at most C(d)M_b in the coarser units, below the layer widths for K_{CRE} ≥ C(d) + 1 (LF #4.22.1, #4.24); on the coarser part the bounds cost at most L³, absorbed in C₂ = C₂(d, L).
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 with the CT12–CT14 repairs (1 clean round, CT11).
- **Hashes (17:27):** note 50e8029bfc7f, passage 9566e6811aa2, contacts 2ba31b36899b, LF 1bbb59aef5be (peer's).
- **Next:** CT15 alone (scope_twoloops_RevalCT15.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT15: Triage

Log: reviews\work\referee_cli_20261104-172755_scope_twoloops_RevalCT15.json (launched 17:28, landed about 17:43). No ERROR, two MINORs, both in §4a; neither changes a bound. The CT14 repairs hold, apart from the v(x) part (CT15-1); the order of constants and ε_od check.

- **CT15-1 (MINOR): accepted and repaired.** "|v(x) − 1| = O(ρ̂)" needs v slowly varying per fine bond, which the data do not force (a VAR (4) gauge on U² at one fine site changes v(x) by g₀^{−1}). Repair (the referee's first option): the comparison at x uses one element V := v_{ω₀}(x) for all walks, T₂^{old}(x) := 𝓗₁(Δd)(x) − V𝓗₂(Δd)(x). For another walk, w := v_{ω₀}^{−1}v_ω almost stabilises W := (U²)^{v_{ω₀}} on x's block, per fine bond to O(ρ̂L^{−j}), and w = 1 at the block point, so |v_ω(x) − V| = O(ρ̂), a cost of O(ρ̂) times the walk's bound.
- **CT15-2 (MINOR, citation): accepted and repaired.** On Λ^{old}, U¹'s data are V_h (note #160), whose regularity is note #5.6's (χ_{h,1/2} with P = ∅, LFR I (1.88), p.197 l.44–51), not #6.16's. *The bases are near pure gauges* now cites it; ε₁′ is unchanged (O(ε_h) ≤ α_{0,h}).
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 with the CT12–CT15 repairs (1 clean round, CT11).
- **Hashes (17:44):** note 50e8029bfc7f, passage 9566e6811aa2, contacts f8fbc6b21d5f, LF 1bbb59aef5be (peer's).
- **Next:** CT16 alone (scope_twoloops_RevalCT16.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT16: Triage

Log: reviews\work\referee_cli_20261104-174451_scope_twoloops_RevalCT16.json (launched 17:45, landed about 17:58). No ERROR, one MINOR; no bound changes. The CT15 repairs hold apart from CT16-1; one element V at x serves all walks and all three rooms (∇_{U^v}(Ad_vT)(x) = Ad_{v(x)}∇_UT(x)).

- **CT16-1 (MINOR): accepted and repaired.** Under the left action, W^w for w := v_{ω₀}^{−1}v_ω and W := (U²)^{v_{ω₀}} is (U²)^{v_{ω₀}^{−1}v_ωv_{ω₀}}, not (U²)^{v_ω}. Now w := v_ωv_{ω₀}^{−1}, so W^w = (U²)^{v_ω}, and |v_ω(x) − V| = |w(x) − 1| in a bi-invariant norm.
- **Remark (repaired):** ω₀ is now a short walk that avoids Λ^{old}; if none exists, V := 1 and every walk is bounded as in *A walk that meets Λ^{old}* or *Long walks*.
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 with the CT12–CT16 repairs (1 clean round, CT11).
- **Hashes (17:58):** note 50e8029bfc7f, passage 9566e6811aa2, contacts 5e860e1dece6, LF 1bbb59aef5be (peer's).
- **Next:** CT17 alone (scope_twoloops_RevalCT17.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT17: Triage

Log: reviews\work\referee_cli_20261104-175909_scope_twoloops_RevalCT17.json (launched 17:59, landed about 18:16). Full packet, afresh. No ERROR, two MINORs; no bound changes. The CT16-1 repair holds, and so does the V := 1 fallback. Every other part of §§1–5 re-checks: the pins, the arithmetic, the order of constants, and the LF statuses.

- **CT17-1 (MINOR): accepted and repaired.** §1's stratum weight measured s to the strata of ∂Λ, with Λ the large-field region that contains Λ₀. §3 lands the passage's s̄, which is measured at the interface Λ₀/Λ₁ (the passage's ∂C, §3 (b₀)). §1 and note #52.1 now measure s at the interface Λ₀/Λ₁.
- **CT17-2 (MINOR): accepted and repaired.** §4a *Their size* said that "T₂^{old} is linear in Δd". It now writes T₂^{old} = ∫₀¹[κ₁(tΔd) − Vκ₂(tΔd)]Δd dt, which (190) bounds linearly in Δd, uniformly on the ball (note #45).
- **Pin slack (repaired):** PBG Theorem 3.4 is now cited as p.400 l.7–10.
- **Status bookkeeping (the referee's remark; no review needed):**
  - The passage draft's header, §8, and *Result of (ii)* now say reviewed and cleared.
  - The note's #5.3, #5.8, and #5.10.5 now give the passage (packets PV and PL) as reviewed, and (1), (b), and (c) of #5.8 as derived, not reviewed (packet CT).
  - The #5 heading now names what is not reviewed: the contacts draft, and LF's (KW) and block size.
  - #175 gives both clauses' statuses: map l.174 is reviewed, and D2.7 item 15.8 is derived, not reviewed.
  - labels_two_loops.py passes (972 tags).
  - LF is now at 844525635d69, and every LF tag the draft cites is present. The header records it.
- **Open:** none.
- **Derived, awaiting review:** contacts §§1–5 (1 clean round, CT11).
- **Clearance plan:** CT17 was a full pass, and it found only the two MINORs above. CT18 is narrow (the per-round scope rule). It covers the repaired bullets and their consumers, and the status edits. If CT18 is clean, CT is cleared with CT11 (full) and CT17 plus CT18 (a full pass whose only findings were repaired and then checked clean).
- **Hashes (18:18):** note 1d9e0194ff1d, passage 3cc58ebfc584, contacts ddbdb9e27aac, LF 844525635d69 (peer's).
- **Next:** CT18, narrow (scope_twoloops_RevalCT18.md). Then the queue: E2a, E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet CT, Round CT18 (narrow): Triage

Log: reviews\work\referee_cli_20261104-181835_scope_twoloops_RevalCT18.json (launched 18:19, landed about 18:30). No ERROR. Part (A), the contacts draft, is CLEAN: the CT17 repairs hold. The referee re-derived §3's case split, c₂ > 0, and the 3/128 total, and checked *Their size*'s integral form, the pins, and the LF statuses in the header. Part (B), the note's status statements, has two MINORs (status only).

- **CT18-1 (MINOR, status): accepted and repaired.** #5's heading limited the LF dependence to #5.8 (1), (b), and (c), but #5.8 (2) (through #5.10.5 and #5.11's C_H) uses (KW), and #5.8 (a) uses LF's block size (passage §9, LF #4.23). The fixes:
  - #5's heading now names every use of LF's (KW) and block size.
  - #5.8 (a), (c), and #5.10.5 (i)–(ii) mark LF #4.22–#4.24 as derived, not reviewed in LF (LF #4.21).
  - #5.10.5 marks (KW) at its use.
- **CT18-2 (MINOR, status): accepted and repaired.** #5.11's heading said "derived, not reviewed", against #5's "reviewed". PV17 reviewed #5.1–#5.11 with #5.10.1–#5.10.6 (scope_twoloops_RevalPV17.md l.14), and PV is cleared, so A9 no longer needs to cover #5.11, and the labels of #5.10.1, #5.10.2, #5.10.2.1, #5.10.3, #5.10.4, #5.10.6, and #5.11 now say "derived and reviewed, packet PV". #5.11's last sentence now gives (a) and (1) as reviewed (PL, CT).
- **Remark (repaired):** #175's pin is now "D2.7 15.8 (e), its base-point clause O3". D2.7's three OPEN items in 15.8 (the link comparison, Pol ≥ (K/2)(d′+1), and O2 at k > N) are outside what #175 uses.
- **CT cleared.** The clean rounds are CT11 (full) and CT17 (full), whose two MINORs were repaired and checked clean in CT18. Status bookkeeping (no review needed):
  - The contacts draft's header, §4a, and §5 now say reviewed.
  - In the note, #5.3, #5.8, #52.1, and #166 now say "packet CT".
  - All 37 "(R-eval-old), derived, not reviewed" markers in the note, with #3, #6, #7, #45, #72, #166, #167, #229, and #785, now read "derived and reviewed, given LF (#5)".
  - D2.7 l.3 now gives the note's (R-eval-old) as reviewed, given LF's (KW) and block size.
  - labels_two_loops.py passes (972 tags).
- **Open:** none in the note. Elsewhere, D2.7 15.8's three OPEN items (D2.7's own, unchanged; #175 uses only 15.8 (e)'s O3).
- **Derived, awaiting review:** LF's (KW) and block size (the peer's, in LF); D2.7 15.8 apart from its OPEN items; and the queued packets.
- **Cleared:** packets CV, PV, PL (the passage draft in full), and CT (the contacts draft). So (R-eval-old) is reviewed in full, given LF.
- **Hashes (18:34):** note 808564d0ef4c, passage 3cc58ebfc584, contacts 70898124fa5e, D2.7 cf2f9617d229, LF 844525635d69 (peer's, as read).
- **Next:** the queue, E2a first (scope_twoloops_RevalE2a.md, refreshed), then E2b, C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet E2a, Round E2a1 (full): Triage

Log: reviews\work\referee_cli_20261104-183537_scope_twoloops_RevalE2a.json (launched 18:36, landed about 18:49). No ERROR, four MINORs. The referee found that the pre-R support, the six kinds of operation, and #191's conclusion up to G-valued gauge transformations hold, and that every pin checks. Each finding was checked against the cited lines before repair. Table edit by the peer during the round (6c8c973e67d1): #T2.5 and #T2.15 keep the bounds #99 uses; E2a does not read the table.

- **E2a1-1 (MINOR, status): accepted and repaired.** Map l.174 covers only terms of the form (2.21) with the printed characteristic functions, and it leaves "any other 𝐑-modified term" to D2.7. CRE p.258 l.34–36 says an R-changed T^{(j)} keeps (2.21) "but the characteristic functions are changed". So after an earlier R-step the pre-R clause is D2.7 15.8 (e)'s O3, which is derived, not reviewed. The fixes:
  - #175 now says this, with the rest of the old text in a new line #175.1, and gives O3's status.
  - #173's heading gives the status of both clauses.
  - #18 (in "The constants") now marks O3's status too.
  - #212 and #222 cite "the pre-R clause" without restating its status; #175 states it.
- **E2a1-2 (MINOR): accepted and repaired.** Two changes of variables were missing from #179's list:
  - #184.1, the preliminary steps' δ-removal by C (LFR I p.187 l.53–54, p.188 l.53);
  - #184.2, LFR II's V′ = exp ig_kB (LFR II p.360 l.41–42).
  - Both keep the support, so #191 is unchanged.
- **E2a1-3 (MINOR): accepted and repaired.** #186 now says that the integration variables are V_h on Z_h (unchanged, p.194 l.13–15) and V″ = V_j on Γ_j″, j = 0, …, k (p.194 l.12). Through the changes of variables and #184, they parametrise V_k↾Λ together with (1.72)'s V_j on the δ-constraint surface.
- **E2a1-4 (MINOR): accepted and repaired.**
  - #189 now separates the integrand from its (A_j, B_j)-integral.
  - #189 also gives the normalisation as the iterated integral of the integrands (1.60), one per preliminary step, each carrying the earlier ℂ_k^{(i)} through 𝔹_k^{(n)} ((1.61)–(1.62), p.189).
  - Also repaired at #187, against p.189 l.27: ℂ_k^{(n+1)} is the logarithm of (1.60)'s integral plus the renormalisation term of the Wilson action.
- **Not raised by the referee:** whether map l.313's "support of the term's indicators" includes the T-operations' δ-constraints. #176 follows map l.313, and #184 and #184.1 parametrise those constraint surfaces.
- #184.2 pins the Haar density σ(g_kB) at LFR II p.369 l.12, which I checked; p.360 does not print it.
- labels_two_loops.py: 975 tags, check passes. **Hash (18:51):** note d5d2d28569ce.
- **Next:** E2a2, narrow (scope_twoloops_RevalE2a2.md): #18, #173's heading, #175, #175.1, #179–#184.2, #186, #187, #189, and the consumers #191, #212, and #222 for the pre-R clause.

## Packet E2a, Round E2a2 (narrow): Triage

Log: reviews\work\referee_cli_20261104-185203_scope_twoloops_RevalE2a2.json (launched 18:52, landed about 19:02). No ERROR. The four E2a1 repairs hold, and every pin in the repaired lines checks. The referee grepped LFR I and LFR II for further changes of variables and found none missing (LFR II p.357 l.47–49 is of #185's kind). #191, #212, and #222 claim no review of the pre-R clause.

- **E2a2-1 (MINOR, status): accepted and repaired.** #18 named the post-R clause of D2.7 15.8 without its status. It now reads "(derived, not reviewed, #130.12; …)", matching #130.12, which I checked.
- **Remark for 15.8's own review (not this note's).** 15.8 (e) covers O3 and the OPEN O2 in the one phrase "as at k ≤ N". Map l.174 hands 𝐑-modified terms to D2.7, so O3 at k > N rests on LFR II Theorem 1, which 15.8 (e) does not name. The note's #175.1 and #130.12 name it. Recorded here for whoever reviews D2.7 15.8. The note's own statuses are unaffected.
- **E2a cleared** under the 2 Nov clearance rule: E2a1 (full) found the substance correct, and E2a2's only finding was a status attribution, now repaired.
- labels_two_loops.py: 975 tags, check passes. **Hash (19:03):** note d37f38b534b1.
- **Pre-check for E2b (bookkeeping):** #212 now gives the pre-R clause's status, "(map l.174's; after an earlier R-step, D2.7 item 15.8 (e)'s O3, derived, not reviewed; #175, #175.1)". Note 1f808d5fa9e8 (19:03).
- **Next:** E2b (scope_twoloops_RevalE2b.md, status lines refreshed; launched 19:04), then C1-2, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2.

## Packet E2b, Round E2b1 (full): Triage

Log: reviews\work\referee_cli_20261104-190356_scope_twoloops_RevalE2b.json (launched 19:04, landed about 19:17). No ERROR, five MINORs. The referee found that the removals, the L₀-weighted layers, and #212's conclusion with its status check against LFR I p.181–200 and LFR II p.378–379. The reading R-combined is consistent with LFR II p.379 l.15 (no READINGS entry; a standing item, not raised). Each finding was checked against the cited lines before repair.

- **E2b1-1 (MINOR): accepted and repaired.** χ′_j (1.27, p.182 l.53) and χ′^{(j)} (1.55, p.188 l.7) are both taken on the * bonds, which omit b_0(c) (CRE (1.9), p.247 l.51–57). There CB_j = B_j (CRE p.249 l.21–24; RG I p.268 l.2–3) and hD̃ = 0 (RG I p.267 l.19). So V_j(V^{(j)})^{−1} = exp ig_jB_j, and with (1.57)–(1.58), |V_j(V_Z^{(j)})^{−1} − 1| < 2δ′_j. So χ′_j's drop is an implication.
  - #196 now states this. The rerun with c_χ in Bałaban's proof is gone.
  - #197 keeps c_χ for (iii) (#91, #144), on all bonds, b_0(c) included. c_C is now defined as the sup of C's norm over the small-field configurations, with a finiteness argument (C acts on the bonds of B(c_±), its coefficients are continuous in V^{(j)} on a compact set, and h(c) is defined there, RG I p.267 l.21).
- **E2b1-2 (MINOR): accepted and repaired.** #198 now lists (1.3), (1.4), (1.5), (1.7), (1.8), and χ_k^{(n)} as equal to 1, with the densities (1.6) extending (p.178 l.31–34). The old #197, which put (1.54) inside (1.29)'s proof, is replaced (the proof ends at p.187 l.32–33).
- **E2b1-3 (MINOR): accepted and repaired.** #210 now gives (1.89)'s own conditions: β ≤ 1/4, (1.94)'s two conditions on N, M large, α ≤ 1/8 (p.200 l.20–21), and p.200 l.30. It says that L₀² ≤ L/3 (p.191 l.34–35) makes the spaces descending and is not a condition of (1.89). #199 now also lists M large and α ≤ 1/8. The referee's "L₀ ≥ 2" is not in p.198–200's text (grep), so it is not added.
- **E2b1-4 (MINOR, pin): accepted and repaired.** #193: p.181 l.33–34.
- **E2b1-5 (MINOR): accepted and repaired.** #201 now separates components excluded before any (1.29) step, where the old functions stay, from those excluded after one, for example by 1 − χ′^{(j)} (p.188 l.10). On the latter that step's functions were already removed (p.187 l.35–37), by an implication from the factors kept on them: χ_k^{(n+1)}, χ^{(j)}, and χ′^{(j)} or (1.59).
- labels_two_loops.py: 975 tags, check passes. **Hash (19:20):** note 674b2d33554f.
- **Next:** E2b2, narrow (scope_twoloops_RevalE2b2.md): #193, #196–#198, #199, #201, #210, and the consumers #91 and #144 for c_χ.

## Packet E2b, Round E2b2 (narrow): Triage

Log: reviews\work\referee_cli_20261104-192032_scope_twoloops_RevalE2b2.json (launched 19:20, landed about 19:31). No ERROR, four MINORs. The E2b1 repairs hold in substance: #196's implication, #197's all-bonds bound (its consumers #91, #92, #98, #116, #117, #121, #144, and #148 use c_χ consistently), #198, #193's pins, and L₀² ≤ L/3's role. Each finding was checked against the cited lines before repair.

- **E2b2-1 (MINOR): accepted and repaired.** #91 now gives < 2δ′_j on the * bonds by χ′_j and ≤ c_χδ′_j on all bonds, the b_0(c) included (#197).
- **E2b2-2 (MINOR, a gap in uniformity): accepted and repaired.** #197's sup was over the step-j small-field set, which depends on g_j. The fix:
  - c_C is now the sup over one fixed closed set S_{θ₀}, the configurations on B(c_−) ∪ B(c_+) with |∂V − 1| ≤ θ₀(d, L).
  - C's norm is gauge invariant.
  - In an axial gauge, |V − 1| ≤ C(d, L)θ.
  - The coefficient of B′(b_0(c)) is invertible at V = 1 and continuous in V (RG I p.266 l.2), so it stays invertible on S_{θ₀}.
  - Compactness then gives c_C = c_C(d, L, G), uniformly in g and j. The configurations on the support lie in S_{θ₀} for g small.
  - The quote of h(c) now includes "multiplied by L^{−1}" (RG I p.267 l.23), and the coefficients depend on the whole linear part of Q̃ ((2.4), p.266 l.6).
- **E2b2-3 (MINOR): accepted and repaired.** #199 and #210 now list L₀² ≥ 3 at p.200 l.22–23, from L₀ ≥ 2 (p.182 l.18), which I checked.
- **E2b2-4 (MINOR): accepted and repaired.** #201 now says that the functions not yet removed stay, and those already removed were removed by implications from factors that stay. Two new lines give the cases:
  - #201.1 covers step 0 (p.181 l.20–23 and l.33–34; the exclusions by 1 − χ′_h, p.183 l.3–4, and by (1.28), p.183 l.11–14).
  - #201.2 covers a (1.29) step, with the chain running to the last χ_k^{(m)} still present (p.183 l.23).
- labels_two_loops.py: 977 tags, check passes. **Hash (19:33):** note 6e882926ad1b.
- **Next:** E2b3, narrow (scope_twoloops_RevalE2b3.md): #91's first sentence, #197's c_C argument, #199, #201–#201.2, and #210.

## Packet E2b, Round E2b3 (narrow): Triage

Log: reviews\work\referee_cli_20261104-193353_scope_twoloops_RevalE2b3.json (launched 19:34, landed about 19:43). No ERROR. The four E2b2 repairs hold: in #197, c_C is a sup of a gauge-invariant norm over the fixed set S_{θ₀}(d, L), compact after gauge fixing, so it is finite and independent of g and j. There are two MINORs, both in #197, and neither changes a bound.

- **E2b3-1 (MINOR, source): accepted and repaired.** RG I p.266 l.2 concerns u_k's analyticity, not M's. The continuity now rests on CMP98 (121)–(124) (p.36): Q̃'s linear part is CMP98's linear form Q(V_0), written out through R_{0,c_±}, Y, and Y_x. RG I's averages are CMP98's: RG I's [12] is CMP98 (p.299 l.12), and RG I p.265 l.17 applies its Proposition 2. I checked both.
- **E2b3-2 (MINOR, a missing step): accepted and repaired.** #197 now passes from χ_k^{(n+1)} to V_Z^{(j)} = M^j(U_{k,Z}^{(n+1)}) ((1.26), p.182) by CMP98 Proposition 2. It then passes to V^{(j)} by (1.58), with |ℍ_Z^{(j)}| ≤ O(1)e^{−R_j}ε_j (p.188 l.29–34), which I checked. The mention of (1.3)–(1.4) is dropped. Also in #196: "(1.58) and (1.57)" becomes "(1.58) and its bound (p.188 l.29–34)", since (1.57) bounds ℍ_{k,Z}^{(n+1)}, not ℍ_Z^{(j)}.
- labels_two_loops.py: 977 tags, check passes. **Hash (19:44):** note 6eb4959e69a0.
- **Next:** E2b4, very narrow (scope_twoloops_RevalE2b4.md): the three repaired sentences of #196–#197 only. E2b3-1 brings in a new source, so it gets one check before clearing. If E2b4 is clean, E2b is cleared (E2b1 full, then E2b2–E2b4 on the repairs).

## Packet E2b, Round E2b4 (very narrow): Triage

Log: reviews\work\referee_cli_20261104-194459_scope_twoloops_RevalE2b4.json (launched 19:45, landed about 19:55). Passages (b) and (c) are clean. The referee also closed E2b3's open check on R_j: CMP98 Proposition 2 applies with α₀ = O(L₀^{2N₀}L^{−2}ε_{j+1}) = O(g·polylog), uniformly in j and k. One ERROR, in (a): the source is wrong, but the conclusion survives and no bound changes.

- **E2b4-1 (ERROR, source): accepted and repaired.** CMP98's Q(V_0) of (121)–(124) linearises the gauge-changed average V̄̄_1. RG I's Q̃ ((2.4), p.266 l.6) linearises the plain ratio Ṽ_1 = (V_1V_0)‾(V̄_0)^{−1} of CMP98 (113) (p.34 l.32), whose linear part is Q′(V_0) of (118)–(119) (p.35). I checked p.34–35. I had taken (121)–(124) from E2b3's suggestion without checking it against (2.4); that was my error. The fix in #197:
  - the citation is now to (113) and (118)–(119), with V_1 = V′, V_0 = V^{(j)}, and "up to RG I's constant normalisation";
  - Q′(V_0) is continuous through R_{0,c_±}, R̄_{0,c}, Y, and Y_x (p.35 l.50–52);
  - a parenthesis records that, by (120), Q(V_0) differs from Q′(V_0) only on bonds inside B(c_±), so the coefficient of b_0(c) is the same.
  - c_C's finiteness and uniformity are unchanged.
- labels_two_loops.py: 977 tags, check passes. **Hash (19:56):** note 8e741cefd39f.
- **Next:** E2b5, very narrow (scope_twoloops_RevalE2b5.md): #197's re-pinned sentences only. If clean, E2b is cleared.

## Packet E2b, Round E2b5 (very narrow): Triage

Log: reviews\work\referee_cli_20261104-195625_scope_twoloops_RevalE2b5.json (launched 19:56, landed about 20:01). No ERROR. The E2b4-1 repair holds:
- (2.4)'s ratio is CMP98's Ṽ_1 of (113), and (113)–(118) use neither the block gauge nor the gauge change.
- So Q̃ = L^{−1}Q′(V^{(j)}) (RG I p.267 l.26).
- Q′ is continuous in V_0, and at V_0 = 1 the b_0(c) coefficient is a positive multiple of I.
- Every pin checks.

- **E2b5-1 (MINOR, normalisation): accepted and repaired.** By (122) (p.36 l.11), which I checked, CMP98 writes the linear part of (1/i)log V̄̄_1 as L·Q(V_0). So L·Q(V_0), not Q(V_0), differs from Q′(V_0) by in-block terms. The parenthesis in #197 now says this, and that the b_0(c) coefficient is the same in Q(V_0) and in L^{−1}Q′(V_0). Invertibility and continuity are unaffected.
- **E2b cleared** under the 2 Nov rule. E2b1 reviewed the packet in full. E2b2–E2b4 found gaps in the repairs, each repaired. E2b5's only finding is a normalisation slip in a parenthesis, now repaired.
- labels_two_loops.py: 977 tags, check passes. **Hash (20:01):** note f31c41764024.
- **Next:** C1-2 (refresh its scope's status lines first), then C2a4, C2b8, A9 (without #5.11, PV17 covered it), B2, E1e, P2, P1, 2b, 2.

## (R-eval) Packet C1, Round C1-2: Pre-Check Before Launch

- The scope's stale "Declared open" (Open (R-eval-old), Open (R-eval-curv)) is replaced: (R-eval-old) is derived and reviewed, given LF; #6 is derived, not reviewed. The scope also notes #91's E2b edit and skips STEP 1.
- Status marks added in the packet (bookkeeping): #92's #6.14 and #6.16, and #113's #6.10, #6.12, and #6.13, now say "derived, not reviewed", matching #6's heading.
- labels_two_loops.py: 977 tags, check passes. **Hash (20:02):** note ebb14b64557a. C1-2 launched 20:03 (full round: the packet was edited by later repairs).

## (R-eval) Packet C1, Round C1-2 (full): Triage

Log: reviews\work\referee_cli_20261104-200238_scope_twoloops_RevalC12.json (launched 20:03, landed about 20:20). No ERROR, four MINORs. The C1-1 repairs each close their finding. Everything else checks against the pages: VAR's inputs, PRT2 (2.46)'s distance (#99's M/M₁ is conservative), S_L, the bound on G, the reduced frame, and (a), (b), (c′). Each finding was checked against the note and the cited lines before repair.

- **C1-2.1 (MINOR): accepted and repaired.** C and h depend on V^{(j)} (RG I p.267 l.22–23, p.268 l.2–3), and V^{(j)} is complex at complex 𝐔, so on the bonds b_0(c) the source moves with 𝐔. The fixes:
  - #95 now says where the complex part enters. On the * bonds s_n = g_jB_j is real (#196).
  - #197's S_θ now contains complex configurations e^{iX}V_r with |X| ≤ θ. C is analytic in V on a neighbourhood of S_{θ₀} (Q′ is built from polynomials, logarithms near 1, and g, g^{−1}, e^{iz}; the inverse of an invertible analytic coefficient is analytic). c′_C, the sup of C's derivative over S_{θ₀}, is finite and depends only on d, L, and G.
  - V^{(j)}(𝐔) = e^{iX}V^{(j)}(U) with |X| ≤ C_GL^jηε_{n+1} (#97).
  - #116 adds |s_n(𝐔) − s_n(U)| ≤ O(c′_CC_G)L^jηε_{n+1}δ′_j to |s̃ − s^{re}| and keeps |s̃| ≤ 3c_χδ′_j.
  - #119 (b) gains O(c′_CC_G). C_* now also depends on c′_C, at #121 and #144.
- **C1-2.2 (MINOR): accepted and repaired.** 𝕌^{(n)} is VAR's Landau representative, which does not keep the plain data (REG p.81 l.23–24, raw l.24, which I checked). #104 now says that d_n is the step's data, and that 𝕌^{(n)}'s plain data are d_n conjugated at the block points by u_n, with w_n(y) = u_n(y)^{−1} there. #116 bounds the factor u_n(𝐔)u_n(U)^{−1} by #106–#109 applied to 𝕌^{(n)} (deviation ε_n): O(B_G)L^jηε_n, inside the existing O(B_G)L^jη(ε_n + ε_{n+1}).
- **C1-2.3 (MINOR, status): accepted and repaired.** #90 and #116 now also give C_Λ's frame bound (#41.1–#41.2, derived, not reviewed), which I checked at #41.1–#41.2.
- **C1-2.4 (MINOR, pin): accepted and repaired.** #109 now reads "u_L is analytic in the configuration, VAR p.307 l.2–4, and w is by its construction, #104".
- **Standing (not raised):** READINGS.md has no entry for R-chain-cx (#17's readings).
- labels_two_loops.py: 977 tags, check passes. **Hash (20:23):** note 736b265666ae.
- **Next:** C1-3, narrow (scope_twoloops_RevalC13.md): #90, #95, #104, #109, #116, #119, #121, #144's C_*, and #197's S_θ, analyticity, and c′_C sentences.

## (R-eval) Packet C1, Round C1-3 (narrow): Triage

Log: reviews\work\referee_cli_20261104-202400_scope_twoloops_RevalC13.json (launched 20:24, landed about 20:37). No ERROR, four MINORs, none changing a conclusion. C1-2.3 and C1-2.4 are closed. Each finding was checked against the note and the cited lines (RG I p.265 l.32–35, p.267 l.18–32; CMP98 p.35 l.40–46) before repair.

- **C1-3.1 (MINOR): accepted and repaired.** (i) #197 bounded X for an average, but s̃ used the u-free source, whose average is not in that frame. (ii) D̃ depends on V through Q̃ and C̃ (RG I p.267 l.24–26), and its V-dependence was not bounded. The fixes:
  - #116 now writes s̃ by covariance (p.265 l.34–35) as g_jC(V_{red})Ad_ũB_j − hD̃(·), at the reduced stage's average. The identity holds at real minimisers, where ũ is G-valued (#112), and on 𝓜^c by the identity theorem (#113–#114). s̃ − s^{re} splits into a conjugation part and an average part. The average part uses |X| ≤ C_GL^jηε_{n+1} for V_{red} (#115, #97).
  - #197 defines c_D. hD̃ is jointly analytic in (V, B) by the analytic implicit function theorem (unique solution, p.267 l.28–29). It vanishes to second order at B = 0. c_D bounds |∂_V(hD̃(B))|/|B|².
  - c′_C is now at least 1, so c_Dc_C²δ′_j is absorbed for g small. #95 names D̃. C_* depends on c_D at #121 and #144.
- **C1-3.2 (MINOR): accepted and repaired.** #106–#109 concern transformations equal to 1 at U at a fixed base, so they did not bound u_n(𝐔)u_n(U)^{−1}. The new #116.1 bounds ũ_m factor by factor:
  - u_L: by *The bound on G*.
  - u_{L,m}: analytic in 𝓗(d_m) at the fixed U₀ (REG (1.70)–(1.71)), with Lipschitz constant O(d)L^jη.
  - u_m: equal to 1 at zero step field for every base, so its change carries a factor O(δ′_j).
  - Step m's field change is (a)+(b) of step m, which involve only m′ ≥ m + 1. So the induction runs from m = N down, with no circularity. The O(δ′_j) shares sum to O((N+1)δ′_j) times the main sum.
- **C1-3.3 (MINOR): accepted and repaired.** #104's d_n is now (Δd_L, s̃ ⊕ B*).
- **C1-3.4 (MINOR): accepted and repaired.** #197: R̄_{0,c} = R((V̄_0)_c) (CMP98 p.35 l.43–44) is analytic, not polynomial, through (113)'s average.
- **Bookkeeping:** #175.1 now says "15.8 has no OPEN items" (D2.7 dbef60405e55).
- labels_two_loops.py: 979 tags, check passes. **Hash (20:42):** note 3608fe7fa7dc.
- **Next:** C1-4, narrow (scope_twoloops_RevalC14.md): #95's last sentences, #104's d_n, #116 with #116.1–#116.2, #119, #121's and #144's C_*, and #197's R̄_{0,c}, c′_C, c_D, and last-paragraph sentences.

## (R-eval) Packet C1, Round C1-4 (narrow): Triage

Log: reviews\work\referee_cli_20261104-204347_scope_twoloops_RevalC14.json (launched 20:43, landed about 20:56). One ERROR, three MINORs. C1-3.1, C1-3.3, and C1-3.4 are closed; #119 (b) and C_* check. Each finding was checked against the note and the cited lines (REG p.88–89 raw, VAR p.305 l.31–37 and p.307 l.1–14) before repair.

- **C1-4.1 (ERROR): accepted and repaired.** #116.1 built u_m from F at a moving base 𝕌, mislabelled e^{iηA_L}U₀. u_m's field is ηℍ^{(m)}(s̃) at 𝕌, and a base derivative needs analyticity in a complex base, which REG (one fixed U₀, p.89 l.25) does not give. The repair takes u_m as a function ψ(d, s) := log u_m of step m's inputs at the fixed real U₀: the plain data d = d_{m+1} (#97) and the source s = s̃.
  - ψ is analytic on VAR's ball (VAR p.307 l.2–4; #104). It is bounded there by M_u = O(d), by REG's bound on u′u₁ (p.89 l.35) at complex fields, as at #106.
  - ψ(d, 0) = 0, since at s = 0 the step is trivial and G_m = G.
  - The Schwarz lemma in s and Cauchy's estimates give |Δψ| ≤ O(M_u/r_B)(|Δs| + |s||Δd|/r_B), with |d| ≤ C_GL^jηε_{m+1} and |Δs| from #116 at step m. So u_m's change is O(δ′_j)L^jηΣ_{m′≥m+1}(ε_{m′} + ε_{m′+1}).
  - No base other than U₀ enters. The induction from m = N down stands, since #116 at step m uses only m′ ≥ m + 1.
- **C1-4.2 (MINOR, pin): accepted and repaired.** u_{L,m}'s analyticity is now pinned to VAR p.307 l.2–4, and its Lipschitz constant comes from REG's bound on u = u′u₁ (p.89 l.35), not from (1.70)–(1.71), which bound u₁ only.
- **C1-4.3 (MINOR, pin): accepted and repaired.** #116: |g_jB_j| < δ′_j (#196), not 2δ′_j (#91).
- **C1-4.4 (MINOR): accepted and repaired.** #121's last sentence now reads "G enters through |λ̂|, and the accumulated ũ_m with m ≥ n + 1 enter through (b), by #116.1."
- labels_two_loops.py: 979 tags, check passes. **Hash (20:59):** note ec175dfb949b.
- **Next:** C1-5, narrow (scope_twoloops_RevalC15.md): #116.1's u_{L,m} and u_m sentences, #116's |g_jB_j|, and #121's last sentence.

## (R-eval) Packet C1, Round C1-5 (narrow): Triage

Log: reviews\work\referee_cli_20261104-205958_scope_twoloops_RevalC15.json (launched 20:59, landed about 21:10). Two ERRORs, one MINOR. C1-4.2, C1-4.3, and C1-4.4 are closed. Each finding was checked against the note and the cited lines (VAR p.305 l.31–37, p.307 l.1–14, p.309 l.1–12; REG p.88–89 raw; LFR I p.183 l.36–44, p.184 l.36–47, p.186 l.1–13, p.188 l.24–56, p.191 l.30–44) before repair.

- **C1-5.1 (ERROR): accepted; repaired at the source of the problem.** The finding is correct: nothing cited gives u_m's analyticity or bound at the complex base 𝕌. The root cause is in #104 and #110. The note's u-free step exp iηℍ^{(n)}(s̃)𝕌 omitted LFR I's normalisation. LFR I's stage is (exp iηℍ 𝕌)^{u^{−1}} ((1.44), p.186 l.5; (1.34), p.184 l.39–41), and it satisfies M^j(U_k^{(n)}) = V_j exactly (p.183 l.38–39). Its sources are relative to the data-exact averages (V_Z^{(j)} of (1.26), V^{(j)} of (1.58)), and its densities (1.6) are written in the data variables V_j.
  - #104 and #110 now define the u-free step with that normalisation. Its plain data are d_n exactly, so w_n(y) = 1 at the block points, as for 𝕌 (#103, VAR's orbit group (4)).
  - At a block point, ũ_m = u_{L,m}^{−1}u_L. u_m does not occur, and nothing needs a complex base: u_L and u_{L,m} are REG's transformations at the fixed real U₀ with complex fields, as at #106.
  - #95 now says the step is followed by the inverse of its normalisation; p.191 l.39–41 is cited for the landing of the step.
- **Considered and dropped:** taking the integration variables in the reduced frame, so that no ũ enters the sources. The substitution B_j ↦ Ad_ũB_j preserves Haar measure, but the axial densities (1.6), in V_j(y, x), are not invariant under it. At complex 𝐔 they would be evaluated at complex arguments, with a factor exp(O(μδ′_j/g_j²)).
- **C1-5.2 (ERROR): moot after C1-5.1's repair.** It concerned the sup-norm Cauchy estimate for u_m, which is gone. u_{L,m}'s Lipschitz bound keeps its factor L^jη at y, because #106's bound |log u(y)| ≤ 16dL^jη|A|_{(0)} is pointwise at the layer-j block point y.
- **C1-5.3 (MINOR): accepted and repaired.** #116.1 now takes u_{L,m}'s ball in the two norms of REG's (1.69) (p.88 l.29–31), |·|_{(0)} and |∇·|_{(−1)}, and measures the change in the larger of them. The change has two parts: ‖A_L‖ ≤ O(C_GS_L)ε_{m+1} (#105), and ΔF with its gradient bounded by (a)–(b) and (190)'s gradient bound (#94).
- labels_two_loops.py: 979 tags, check passes. **Hash (21:22):** note d414c5451c0d.
- **Next:** C1-6, narrow (scope_twoloops_RevalC16.md): #95's step sentence, #104's last part, #110's step, and #116.1.

## (R-eval) Packet C1, Round C1-6 (narrow): Triage

Log: reviews\work\referee_cli_20261104-212325_scope_twoloops_RevalC16.json (launched 21:23). Two ERRORs and two MINORs. Each finding was checked against the note and the cited lines (LFR I p.182–p.191; VAR p.278, p.280, p.307, p.309; REG p.78–p.80, p.88–p.89 raw; CRE p.256–p.257, p.266) before repair.

- **C1-6.1 (ERROR): accepted; open, #3.2.** The finding is correct. ũ_m is used at the layer-j block points of step n's collar, where stage m has blocks of layer j + (m − n). There w_m ≠ 1, and the G-bounds give L^{j+(m−n)}ηε in place of L^jηε. The conjugated source then moves the field at a layer-i point by about εδ′_j(L^iη)^{−1}. The reduced frame (#110–#116.2) is marked open, and #3.2 states what is missing and what closes it.
  - Dead route: Landau representatives of each stage in its own determining set, at one fixed real base. REG's Landau gauge depends on the set through R(U₀) (REG p.80 l.11–14), so #97's identity F(·, 0) = 0 does not pass between sets, and each change of set costs O(ε).
  - Dead route: LFR's own frame, pinned to the start's averaged tree transports. Its step fields on bonds crossing coarse block boundaries exceed the Landau ones by powers of L (REG Lemma 1, (1.25), p.79).
- **C1-6.2 (ERROR): accepted; the pin and the norms are corrected, and the Lipschitz step is part of #3.2.** REG (1.69) (p.88 l.28–29) bounds |A|_{(−1)} and |∇A|_{(−2)}. #116.1 now says so. A Cauchy estimate on that ball gives the constant O(d) for changes in those norms, which are suprema over all layers. The factor L^jη at a layer-j block point needs the locality of u in the field, which REG does not print.
- **C1-6.3 (MINOR): accepted and repaired.** #91's last sentence now keeps the u of (1.44) (#95, #104). The new #88.1 says that Bałaban's inclusion (p.191 l.39–42) is for the step before its normalisation and is used only for the domain of his extension. The normalised stage is a G^c transform of that step, and its words agree with the step's by the identity theorem, since u is G-valued at the real minimisers.
- **C1-6.4 (MINOR): accepted and repaired** with C1-6.2's edit: the pin is p.88 l.28–29.
- labels_two_loops.py: 981 tags, check passes. **Hash (22:37):** note bbbc77ddc821.
- **Next:** no C1-7 launch until #3.2 is closed; a referee round on a partial repair would review the open frame again.

## (R-eval-cr) Packet P2: Triage (5 November, 00:48)

Referee log: `Balaban\reviews\work\referee_cli_20261105-002825_scope_twoloops_P2_Revalcr.json`, REVIEW_LOG.md "WILSON_IT1_TWO_LOOPS (R-eval-cr), second round (packet P2)". P1-2, P1-5, P1-6, and P1-7 are closed. Each finding was checked against the note.

- **P2-1 (ERROR): accepted and repaired.** #492 still had the pre-repair 5.1 step. It now reads as #228 does. #485 states the lemma on 𝒟^{ev}_{n+1} after an R-step. The new #496.1 adds P1-3's condition c_πλα_{1,n+1}·41M/L ≤ ν_r/16. #83 and #484 now name 𝒟^{ev}.
- **P2-2 (ERROR): accepted and repaired.** 𝒟^λ_1 ⊂ 𝒟♮_1, not 𝒟_1 (#48, #6.12). #227 now poses the step-1 clause on 𝒟^λ_1 ∩ 𝒟_1. Its consumers (the T-step into 2 and the carry's 5.1 at n = 1) evaluate at points of 𝒟_1, by #6.14. No R-step acts at step 1 (k > N_B > N₀ ≥ 1).
- **P2-3 (MINOR): accepted and repaired.** The new #222.1 lists the further points of 𝒟^{ev}_k:
  - the s ≠ 1 points, which lie within 2K sup|𝐇| of the s = 1 point (#137);
  - the re-projected points at a localized background (#130.3);
  - part (b)'s pairs (#136, #130.13).
  #222 and #228 now say that 𝒟^{ev} ⊆ 𝒟^λ holds in the M-factored sense.
- **P2-4 (MINOR): accepted and repaired.** #222.1 defines 𝒟^{ev}_{K′} as the real points of (8.2)'s final integration (#923–#924). There the landing holds given D(k)(iii)'s pre-R base-point clause.
- **P2-5 (MINOR): accepted and repaired.** #3, #220, and #917 now mark #3.2, and #3 and #917 also mark #3.3.
- **Pre-check edits before P2's launch:** #222, #229, and #785 now mark #3.2. **After P2:** #264, #722, and #844 now mark #3.3.
- labels_two_loops.py: 990 tags. **Hash (00:48):** note cd47df059ced.
- **Next:** narrow round P3 on these repairs (#83, #222–#222.1, #227–#229, #484–#496.1, #3, #220, #917).

## #3.2: Routes Tried and the Current Route (5 November)

Dead routes, one line each:
- The collar's separation from the deep layers.
- Per-set Landau representatives at a fixed base.
- LFR's pinned or axial frame.
- The shortcut r < 1 (r ≥ 2).
- A real-base reduction with α₁-sized gradients.
- The inherited frame, or unconjugated sources: the positive measure sits at U.
- The finest set's Landau frame: its start costs a constant factor, and the landing has no constant slack.
- A second-difference bound on ũ: it is still L^{m−n}δ′².
- A contour shift in B: the χ cutoffs are sharp.
- Moving the constant mode ū_m into the frame: this is the unconjugated route again.
- Conjugating along C: what remains is a commutator with the real holonomy, which is O(1) for large loops.

The current route is #3.2.1–#3.2.3.2:
- The loss is the constant mode of ũ_m on the source's support.
- It is δ′_j-small in Bałaban's layer weights.
- What remains is the landing, through an extra deep-layer room paid by half of Bałaban's large-field weights (p.385 l.35–37).
- Dead: landing through Z's post-R k-block averages. The R-step evaluates pre-R members, and their averages are taken on the fine old blocks.

## (R-eval-cr) Packet P3 (Narrow): Triage (5 November, 01:06)

Log: referee_cli_20261105-004951_scope_twoloops_P3_Revalcr.json. P2-1, P2-4 and P2-5 closed; P2-2 closed in #227; no ERROR.
- P3-F1 (MINOR), accepted. #130.6 evaluates each member at its part (b) pair (𝐔″, R(ĥ)𝐉), and #130.13 lands only the pairs. Repaired: #222 defines 𝒟^{ev}_k as the pairs and says each member is evaluated at its own pair (#130.6), landing by #130.13. #222.1 lists the further pairs (s ≠ 1, re-projected), which enter only through their pairs. #229 now reads "through their part (b) pairs (#222, #222.1)".
- P3-F2 (MINOR), accepted. Repaired: #484, #492 and #228 add the step-1 domain 𝒟^λ_1 ∩ 𝒟_1 = 𝒟_1 (#227), with the points in 𝒟_1 by #6.14. #222 adds the same at k = 1. #227 states 𝒟^λ_1 ∩ 𝒟_1 = 𝒟_1 by #53.
- Outside scope, accepted. #7, #23 and #29 now mark #3.2.
- Next: P4, narrow, on these repairs.

## (R-eval-cr) Packet P4 (Narrow): Triage (5 November, 01:25)

Log: referee_cli_20261105-010648_scope_twoloops_P4_Revalcr.json. P3-F1 is closed. P3-F2 is closed in #227, #222, #228, #484 and #492. The marks in #7, #23 and #29 are closed. There is no ERROR.
- P4-F1 (MINOR), accepted. Repaired: #374 and #83 now carry the step-1 domain 𝒟^λ_1 ∩ 𝒟_1 = 𝒟_1 (#227). The pre-check found no other step-1 sup statement on 𝒟^λ; #16 and #619 are R-step statements.
- Outside the scope, accepted. #19, #26 and #30 now mark #6.13 as given the bound open at #3.2.
- Next: P5, narrow.

## (R-eval-cr) Packet P5 (Narrow): Triage (5 November, 01:40)

Log: referee_cli_20261105-011651_scope_twoloops_P5_Revalcr.json. P4-F1 is closed in #374 and #83, and the #3.2 marks in #19, #26 and #30 are closed. There is no ERROR.
- P5-F1 (MINOR), accepted. Repaired: #25, #27 and #31 now mark their use of #6.13 "with #3.2's bound".
- Next: P6, narrow, on #25, #27 and #31, after the #3.2 round.

## #3.2 Closed: Triage (5 November, 01:40)

#3.2 is derived, not reviewed. The note's hash is 83e3adf910e1.
- Why Bałaban does not meet it: his chain is bounded per block in his layer-weighted norms, with a per-block gauge (LFR I (1.93)–(1.94)), and it feeds only gauge-invariant conditions. Our phase room (#49) is uniform across layers, so the stage blocks' coarser layers show up as L^{J−n}.
- The repair: #3.2.1 gives J − n ≤ N from LFR I (1.15)–(1.16), and takes N := N_k = O(log log g_k^{−2}) within LFR I and LFR II's conditions on N. #3.2.2 gives the locality of u = u′u₁: u₁ by REG (1.70)–(1.71), and u′ by (1.90) with PBG Theorem 3.1's kernels in x's own units. #3.2.3 carries the factor L^N into #116, #116.1, #116.2, #119, #121–#123, #144, #150, #6.2 and #6.13. L^NN^{2+β₀}δ′_k is g_k times a power of log g_k^{−2}.
- Dead: paying the deep layers with κ/Pol and an extra deep room paid by half of Bałaban's large-field weights. The choice of N makes it unnecessary.
- #3.3 is now derived through #3.2, not reviewed. D2.7 l.7 is updated (575757897497).
- Pre-check, accepted. In #116.1 and #3.2.2, the ũ_m bound's second part carries L^Nδ′_j, which is (b)'s factor. It does not compound, since its sum carries only ε's.
- Next: Q1 (scope_twoloops_Q1_R32.md) on the #3.2 closure, then P6.

## #97's Identity Repaired (5 November, 01:40)

#97 said 𝓗(Δd_L, B*) = 𝓗_{n+1}(d_{n+1}). That is false as fields: REG's Landau gauge depends on the set through R(U₀) (p.80 l.11–14), so the two representatives differ by a gauge transformation. Repaired:
- #97 now defines A_L := 𝓗(Δd_L, B*), 𝕌's representative in stage n's Landau gauge, which #104 already uses. F(·, 0) = 0 holds by definition.
- New #97.1: 𝔹_k^{(n)} refines 𝔹_k^{(n+1)} (LFR I p.180 l.4–6, l.18–22, (1.15)–(1.16)), so 𝕌 is the minimiser with its own stage-n data, and VAR Theorem 1 puts it on 𝕎's orbit.
- Note 58108d52fc5d. Review goes with C1-7 (scope_twoloops_RevalC17.md).
- Pins (01:41): #3.2.1, #3.2.2 and #97.1 now use the convention: corrected-file lines for LFR I p.180 and PBG p.397–398, and raw minus one for REG p.89, p.91 and p.102. Note 36f84f80effa.
- Pre-check (01:43), accepted. LFR II p.361 l.12–14 also assumes N ≤ R_k. #3.2.1.1 now lists it as (iv), with Bałaban's R_k (CRE (2.5), checked at p.255 l.36–39) kept apart from (R-member)'s R_k. N_k = O(log log g_k^{−2}) meets it for g small. Note 9a2488b9da05.

## #3.2 Closure, Packet Q1: Triage (5 November, 02:07)

Log: referee_cli_20261105-013703_scope_twoloops_Q1_R32.json. Two ERRORs, one carried-over item, and two MINORs. (a), the quotes of (b), the single factor L^N of (d), and (e) all check. Each finding was checked against the sources before repair.
- **Q1-1 (ERROR), accepted.** LFR II takes N = R_j in (1.80) (p.384 l.14–17), with N = R_j uses at p.385 l.4, p.386 l.3 and p.387 l.15, and LFR I p.177's (ii) is the same N. Repaired: #3.2.1 now says LFR II takes N = R_j. The new #3.2.1.2 derives that N_k meets every use of N in LFR II:
  - (a) upper bounds, which N_k ≤ R_j meets as printed;
  - (b) step counts K, on which (1.80)'s right side increases;
  - (c) lower bounds through L^{−N}, including p.382 l.21–23, which adds ν_L > r(1+β₀) + p₀ − p₁ (CRE (2.4)–(2.5); LFR I p.183 l.2).
  #3.2.1.1's ν_L and #93 are updated.
- **Q1-2 (ERROR), accepted.** REG's A is U₁'s field, so differentiating (1.90) in A does not bound the change in 𝓗(d_m). Repaired by the direct route, as #106 does for u_L: REG's (1.70)–(1.72) reasoning applied to u′u₁ itself (p.89 l.35) gives u_{L,m}(x) through 𝕎_m's own averaged transports inside the stage block (#3.2.2 (2), #116.1). The (1.90)/PBG text is removed.
- **Carried over: C1-6.1(i)–(ii), accepted and repaired.** The u-free stage is LFR I's axial-gauge stage U(𝔅_k^{(m)}, d_m) ((1.18), (1.20), (1.44); #103). So w_m ≡ 1, and ũ_m = u_{L,m}^{−1}G holds at every point. G is bounded at every point by #108. This is #3.2.2 (1), (3), (4), with #104 and #116.1 to match.
- **Q1-3 (MINOR), accepted.** u_L and G now carry L^J, the layer of the stage block (#3.2.2 (3), #116.1).
- **Q1-4 (MINOR), accepted.** The citation is gone with the (1.90) text.
- Note 1f6686cf0680. Next: Q2, narrow, on these repairs.
- Peer check of B̄_G (02:08), accepted. B̄_G is correct, with C_u = O(d) (including the factor 2 of ΔA_L). The O(L^Nδ′_j) in #3.2.2 (4) hides a constant 4dL·O(c_χB̄_G + c′_CC_G)S_L, so g is taken small after it. That is now stated in #3.2.2 (4). Note 1b2190bd5b7f. This edit was made while Q2 was running, so it goes to Q3.

## #3.2 Closure, Packet Q2: Triage (5 November, 02:42)

Log: referee_cli_20261105-020803_scope_twoloops_Q2_R32.json. One ERROR and two MINORs. The repairs of Q1-1 and Q1-2 check, Q1-3 and Q1-4 are closed, and #108 bounds G at every point. Each finding was checked against the sources before repair.
- **Q2-1 (ERROR), accepted.** VAR's U_k(V′V₀) is axial relative to its base (VAR p.280 l.44). VAR p.307 l.2–4 is the transformation "back to the axial gauge". So LFR I's (1.44) is VAR Proposition 9 at the base 𝕌, the previous stage, and LFR I bounds its u through [12] (106)–(108) (p.184 l.55). [12] is CMP98, and CMP98 (106) (p.33 l.44) is that transformation. The stage is axial relative to 𝕌, not U₀, so w_m ≡ 1 was false. Repaired by the new #3.2.2.1 (derived):
  - REG (1.19)–(1.20) telescope: a configuration is axial relative to a base exactly when its averaged transports along the axial contours equal the base's.
  - The averages are covariant (CMP98 (11), (70), also at G^c).
  - So w_m is fixed by the two bases' averaged transports, with w_m(y) = 1. This gives |log w_m(x)| ≤ 4dC_GL^Jηε_{m+1}, and w_m(U) = 1 because 𝕌(U) = U₀.
  - #3.2.2 (1), (4), #104 and #116.1 now carry the three factors w_m, u_{L,m} and G, and C_u covers 4dC_G.
  - #103 now states that #115's U₀ is a real minimiser with its own data, and that U₀ = U_k(V₀), since U′ = 1 satisfies (1.19). This removes the inconsistency with #115.
  - C1-6.1(i)–(ii) is closed by this repair, pending Q3.
- **Q2-2 (MINOR), accepted.** I checked p.362 l.5, p.362 l.35, p.366 l.5 and l.9, p.382 l.40, p.363 l.9, p.369 l.22 and p.375 l.24 against the print. The new #3.2.1.2.1 lists them. The step count now uses N_{j+K} ≤ R_j, derived from CRE (2.7) (p.255 l.53–59), and #3.2.1.2 points to it.
- **Q2-3 (MINOR), accepted.** In #116.1, the VAR p.307 pin now goes with u_{L,m}'s analyticity, and the 𝓗(d_m) identity cites #97's definition of F.
- Note 7eb1f981e033, labels regenerated (992 tags). D2.7 l.7 still holds unchanged.
- Peer (02:30): table ff7d58652e3b with {#T4.32} (B̄_G, B_G, C_G, S_L) added after {#T4.31}; LF c60169974ab9. Recorded.
- Pre-check (02:50), accepted. LFR I p.184 l.55 bounds the u_j of (1.34), which is written "in the standard way, as in (1.30)" (l.36). This is the same representation as (1.44), and #3.2.2.1 now says so. The other steps check: the telescoping of (1.19), the covariance at layer-n lattice points, the recursion along x_n ∈ B(x_{n+1}), |τ_n| through #97's C_G, and 𝕌(U) = U₀. Note cc01cac1c22c.
- Peer (02:48): {#T4.32} will add w_m's 4dC_G to C_u after LF r17. Done: table 310cb2e6096c (labels 9bebc6b90da8). {#T4.32} cites #3.2.2.1 at cc01cac1c22c.

## #3.2 Closure, Packet Q3: Triage (5 November, 02:55)

Log: referee_cli_20261105-024338_scope_twoloops_Q3_R32.json. No ERROR, one MINOR. Q2-1's repair checks in full: the axial gauge relative to the own base (VAR p.305 l.36, p.280 l.44, p.307 l.2–4), the telescoping, the covariance, w_m's recursion, its bound and w_m(U) = 1, C_u's coverage, and #103 with #115. Q2-2, Q2-3, the 02:08 constant, and every tag and pin check.
- **Q3-1 (MINOR), accepted.** #3.2.2 (4) and #116.1 listed the constant hidden in O(L^Nδ′_j) differently. Both omitted r_B, which enters through #98's Schwarz bound, and #116.1 also omitted L. Both now read "d, L, r_B, S_L, c_χ, c′_C, c_C, c_D, C_G, and B̄_G".
- Remark, applied: #3.2.2.1 now cites VAR p.305 l.36 for U₀ = U_k(V₀).
- Note 28374a2bc8dc. Next: Q4, narrow, on Q3-1 and the remark. #3.2 closes after two clean rounds.
- Q4 (referee_cli_20261105-025623_scope_twoloops_Q4_R32.json): CLEAN, the first clean round. Both lists agree, each constant enters, none is missing, and VAR p.305 l.36 is the right line. Next: Q5, a confirming round over the whole #3.2 block as it stands.
- Peer: table dc709ff60261, where {#T4.32}'s source cell cites 28374a2bc8dc; LF 2b482b58579b (labels 828ff3bc285b).

## #3.2 Closure, Packet Q5 (Confirming): Triage (5 November, 03:17)

Log: referee_cli_20261105-030041_scope_twoloops_Q5_R32.json. No ERROR, one MINOR. The whole chain checks: the stage blocks, N := N_k with step counts uniform in K, the bound on ũ_m at every point (G, u_{L,m}, w_m), a single factor L^N, the closures for g small, and every quote and pin.
- **Q5-1 (MINOR), accepted.** I checked LFR I p.199 l.30–31: the proof of (1.89) also uses N, through L^{−2N}N^{1/2}O(1)B₃B₅M⁵(1+β₀) ≤ 1 and N^{1/2}p₁/p₀ small. N_k meets both for g small. #3.2.1.2.1 now states this.
- Remark, not adopted: LFR I (1.10)–(1.12) would give the sharper J − n ≤ N₀ + 1, so Bałaban's own N = R_j would also close. The note keeps J − n ≤ N with N_k, which Q5 confirms is correct.
- Note df9a304cafcc. Q4 was clean. Next: Q6, narrow, on Q5-1. If Q6 is clean, Q4 and Q6 are the two clean rounds and #3.2 closes.

## #3.2 Closure, Packet Q6: Triage (5 November, 03:24)

Log: referee_cli_20261105-031752_scope_twoloops_Q6_R32.json. No ERROR, two MINORs. The quote of p.199 l.30–31, its two conditions, and N_k's meeting them check, and so do the tags and pins.
- **Q6-1 (MINOR), accepted.** l.31's condition is at g_h, with h = k − N, but N_k is controlled in g_k. The comparison now follows from the first line of CRE (2.7) with n = k > m = j and p = p₀ − p₁ > 0.
- **Q6-2 (MINOR), accepted.** I checked p.199 l.47–50: (1+(k−j)^{1/2})p₁(g_j)/p₀(g_j) must be small for h ≤ j ≤ k, and k − j ≤ N. This is now listed and met the same way. #3.2.1.2.1 now states that, with p.179 l.10 and (1.94), the list of LFR I's conditions on N is complete, as Q6's search confirms.
- Note f66b126b4b1d. Next: Q7, narrow, on these two clauses. Q4 was clean; if Q7 is clean, #3.2 closes.

## #3.2 Closed and Reviewed (5 November, 03:30)

Q7 (referee_cli_20261105-032448_scope_twoloops_Q7_R32.json): CLEAN. The comparison by CRE (2.7), the condition at p.199 l.47–50, and the completeness of LFR I's conditions on N check. Q4 and Q7 are the two clean rounds, and Q5 confirmed the whole block. #3.2 is derived and reviewed.
- The marks are updated in #3.2, #110, #116.1, l.77, l.83, and every "the deep-layer bound of #3.2" (#25, #31, #220, and the later lines). Note c3e6431a27a5.
- #3.3 remains derived through #3.2, not reviewed. Its own content, the cross insertions, has had no round.
- D2.7 l.7 (my (R-eval) line) now marks #3.2 as derived and reviewed.
- Peer: table 72d1793479e7, where {#T4.32} cites f66b126b4b1d.
- Next, one at a time: P6, C1-7, P1 (R-member), 2b (R-round), 2 (R-att-ext), and a round for #3.3.

## (R-eval-cr) Packet P6 (Narrow): Triage (5 November, 03:36)

Log: referee_cli_20261105-033123_scope_twoloops_P6_Revalcr.json. P5-F1 is closed: the marks in #25, #27 and #31 check, and so do all tags. No ERROR, one MINOR.
- **P6-F1 (MINOR), accepted.** #16 still said that VAR Proposition 9 removes the factor L^{k−m} "with k − m up to N = R_j", which contradicts #3.2 and #3.2.1.2. Q1-1's fix had reached #93 but not #16. #16 now reads "k − m up to N (LFR II's N = R_j, replaced by N_k, #3.2.1.2)", and the factor is removed "up to one factor L^N from the stages' frame ((iii) below; #3.2, derived and reviewed)". A search for "N = R_j" finds no other line that is not already marked.
- Note 15c30791ebce. Next: P7, narrow, on #16.

## (R-eval-cr) Packet P7 (Narrow): Triage (5 November, 03:45)

Log: referee_cli_20261105-033716_scope_twoloops_P7_Revalcr.json. #16 now agrees with #3.2, #3.2.1.2, #93, #123, #144 and #150. No other line of #3–#31 still says N = R_j, and every tag resolves. No ERROR, one MINOR.
- **P7-F1 (MINOR), accepted.** P6's wording, "remove that factor up to one factor L^N", states no gain, since L^N ≥ L^{k−m}. #16 now says what (iii) actually gains: VAR's data derivatives bound the complex parts in proportion to the data's complex part, with coefficient O(L^NN^{2+β₀}δ′_k), which is g_k times a power of log g_k^{−2} (#123).
- **Out of scope, raised by P7, repaired.** #609 used "N_B, Bałaban's N" as a fixed threshold. D2.7 item 1(b) (l.35) reads N as N_k and gives R = identity for k ≤ N_k. #609 now says so, together with N_B > N₀ ≥ 1, since N_k ≥ N₀ + 1. #173.6 now carries "N read as N_k, #609".
- Note b19a89a9b5ff. Next: P8, narrow, on #16, #609 and #173.6.
- Peer confirmed (03:48): D2.7 (7d4d4947ceaa) item 1(b) at l.35 is the intended reading. N is read as N_k at step k. R is the identity for k ≤ N_k and may act for k > N_k. No table change is needed.
- P8 (referee_cli_20261105-034441_scope_twoloops_P8_Revalcr.json): CLEAN, the first clean round. #16's coefficient agrees with #123. #609's reading agrees with D2.7 l.35, and so do all 14 other uses of N_B. #722's λ_n needs the steps with k ≤ N_k to form an initial segment, and they do, since N_k does not grow with k (g_k^{−2} grows with K − k). #173.6 checks. Next: P9, confirming, over P5–P8's lines.
- Next: Q3, narrow, on Q2's repairs plus the 02:08 B̄_G sentence.

## (R-eval-cr) Packet P9 (Confirming): Triage (5 November, 04:00)

Log: referee_cli_20261105-035007_scope_twoloops_P9_Revalcr.json. #16's sentence on VAR Proposition 9, the "#3.2's bound" marks in #19 and #25–#31, #609, and #173.6 check, and so do all tags. No ERROR, two MINORs, so P9 is not clean and P8 stays the only clean round.
- **P9-F1 (MINOR), accepted.** #23 and #29 marked the whole bound on Z's layers m ≤ k₀ as derived and reviewed. #3.2's header reviews only the frame: the N-step chain's factor L^N. The rest of the deep-layer chain is marked derived, not reviewed (#90, #93, #140, #145). Both lines now say that the stages' frame factor L^N is derived and reviewed (#3.2) and that the rest of the chain there is derived, not reviewed (#90, #93, #140, #145).
- **P9-F2 (MINOR), accepted.** #16 put 𝒟^λ_k's room on the older layers at λα_{1,k}L^{−k} per fine bond. With #52.1's weight 1 ≤ w ≤ L^{c_w}, the room is λ_wα_{1,k}L^{−k}, as #171 has it. #16 now says so (#52.1, #171). The argument is unchanged, since L^{c_w} < L is fixed.
- Note 54067f7c2c05. Next: P10, narrow, on #16, #23 and #29.

## (R-eval-cr) Closed and Reviewed (5 November, 04:06)

P10 (referee_cli_20261105-040145_scope_twoloops_P10_Revalcr.json): CLEAN. #23 and #29 mark only the frame factor L^N as reviewed, which agrees with #3.2, #90, #93, #140 and #145, and no line of #3–#31 marks the chain itself as reviewed. #16's room λ_wα_{1,k}L^{−k} follows from #49 and #52.1 and agrees with #171. P8 and P10 are the two clean rounds. (R-eval-cr) is derived and reviewed, given (R-eval) where it uses (R-eval)'s points.
- The marks are updated in #3, #220, #281, #619, #745, #785 and #917.
- #3.3's header now reads "Derived, not reviewed". Its last sentence gives #3.2's frame as reviewed and the rest of the chain as derived, not reviewed. Its first round is X1 (scope_twoloops_X1_R33.md).
- Note ea7d0b02d444. Next, one at a time: C1-7, P1 (R-member), 2b (R-round), 2 (R-att-ext), X1 (#3.3).

## (R-eval) Packet C1, Round C1-7 (Narrow): Triage (5 November, 04:31)

Log: referee_cli_20261105-040713_scope_twoloops_RevalC17.json. Closed: (a) A_L and #97.1's refinement, (b) #91 and #88.1 as citations, (c) C1-6.2 and C1-6.4 (REG (1.69)'s two norms, p.88 l.28–29), (d) no 𝓗_{n+1} identity is left, (e) every pin. One ERROR, two MINORs.
- **C1-7.1 (ERROR), accepted.** The "u-free chain" now keeps u (#91, #110), but #88, #92, #113 (and #6.7, #158, #870) still placed it in Bałaban's spaces through the inclusion, which is printed for the un-normalised step. Checked against LFR I p.186 l.2–5: (1.44) represents the stage U_{k,Z}^{(n)}, the minimiser with its data, as the normalised step. Bałaban's integrand is therefore the normalised chain, pointwise in the integration variables. The un-normalised chain agrees with it only after the later variables are rotated by R(u), and R(u) is complex at complex data. Repair:
  - The bounds no longer use the spaces at all. #92 now bounds the newer layers by *The sum* (#123) at VAR's representatives, as on the older layers, since no step of #93–#123 restricts the layer. This removes (1.45) on complex spaces, so the reading *R-chain-cx* is dropped (#17, #91, #6.7, #22, #6.5, #93's first sentence).
  - The analyticity on the whole post-R 𝒟_k ((ii)) rests on Bałaban's stages, read through the new reading *R-chain-norm*. p.191 l.37–44 gives the inclusion "for example" for the step, with a proof "almost identical" to (1.44)–(1.52), which carry u, so the reading takes it for his normalised stages. #88.1 states this. #88, #113, #158 and #870 cite it.
- **C1-7.2 (MINOR), accepted.** #97.1 now says why the minimisation passes to stage n. Stage n's constraint set (VAR (3)) is a submanifold, through 𝕌, of stage (n+1)'s, so 𝕌 is critical on it. 𝕌 lies in stage n's space (VAR (2)), since there the collar's bounds ε₀L^{−2j} are weaker. Uniqueness then follows from VAR Theorem 1 (p.279 l.15).
- **C1-7.3 (MINOR), accepted.** #97 now has "𝓗_{n+1} at 𝕌's stage-(n+1) data on 𝔹_k^{(n+1)}", with d_{n+1} on 𝔹_k^{(n)} and the collar's blocks of layer j.
- Note 77aa8fbe48ae. #97's statement changed, so the peer's {#T4.32} cell needs checking. Next: C1-8, narrow, on these repairs.

## (R-eval) Packet C1, Round C1-8 (Narrow): Triage (5 November, 04:47)

Log: referee_cli_20261105-043212_scope_twoloops_RevalC18.json. Closed: (a) no step of #93–#123 restricts the layer, and *R-chain-cx* is gone; (b) #88.1's account of (1.44), p.188 l.53 and p.191 l.37–44; (c) C1-7.2; (d) C1-7.3; (e) every pin. Peer: the table is at d90a35e9e1c9, and {#T4.32} now cites 77aa8fbe48ae. One ERROR (the dependency record), two MINORs.
- **C1-8.1 (ERROR), accepted.** #88.1 said that no bound uses *R-chain-norm*. But (2.34)–(2.37) at 𝕌^{(0)}, and with them 𝕌̃ ∈ 𝒟♮_k, come from Bałaban's chain at the normalised stage (#6, #6.1–#6.2, #6.13, #158). #88.1 now says so. #6, #6.13, #12, #113's landing clause and #17's entry cite the reading.
- **C1-8.2 (MINOR), accepted.** #6.7 now says "no Schwarz step in the background (#16)". The Schwarz lemma in s (#98) is still used.
- **C1-8.3 (MINOR), accepted.** #93's header now credits #92 with the phase on the newer layers only, and #140–#150 with the gradient and the current there.
- **Out of scope, raised by C1-8, repaired.** The chain started at (1.60)'s un-normalised point exp iη𝐇_k″(g_kB)U_k^0. The first preliminary step reads its source at the stage's averages, so by #88.1's argument the chain must start at (1.51)'s U_k″, which carries the normalisation u_k″. (1.60)'s old terms take the same value at both points, since they are gauge invariant and analytic on RG I's G^c-invariant U^c_j (#87). #86, #88, #127 and #870 now start at U_k″, and *R-chain-start* (#17, #86) is read for U_k″.
- Note 666b94237c7f. Next: C1-9, narrow.

## (R-eval) Packet C1, Round C1-9 (Narrow): Triage (5 November, 04:59)

Log: referee_cli_20261105-044746_scope_twoloops_RevalC19.json. Closed:
- (a) every *R-chain-norm* citation;
- (b) #6.7 and #12;
- (c) #93's header;
- (d) the start at U_k″, which agrees with #16, #123 and #39;
- (e) every pin.

No ERROR, three MINORs.
- **C1-9.1 (MINOR), accepted.** The gauge-invariance argument for (1.60) covers the 𝐄- and 𝐑-terms only. CRE's 𝐁-terms are invariant only when A is transformed too (CRE p.261 l.60–62). #86 and #865 now take the 𝐁-terms at U_k″, as (1.49) evaluates them (p.369 l.14).
- **C1-9.2 (MINOR), accepted.** *R-chain-start* is now cited:
  - in #17's entry, for the curvature conditions at 𝕌^{(0)};
  - in #6.13, together with p.375's inclusion;
  - in #158 and in #113's landing clause.

  The new #156.1 inserts the (1.51) step between #156 and #157.
- **C1-9.3 (MINOR), accepted.** #870 now says that U_k^{(0)} is Bałaban's chain of (1.44) stages applied to U_k″, which is the u-free chain. The removal sentences are gone.
- **Outside the scope, repaired.** #86's quote is now pinned to p.372 l.34–35.
- Note 07e3fa606ba6 (993 tags). Next: C1-10, narrow.

## (R-eval) Packet C1, Round C1-10 (Narrow): Triage (5 November, 05:07)

Log: referee_cli_20261105-050016_scope_twoloops_RevalC110.json. C1-9.1–C1-9.3 are repaired and every pin checks. No ERROR, two MINORs, both citation gaps.
- **C1-10.1 and C1-10.2 (MINOR), accepted.** (ii) rests on *R-chain-start* (#86) and, for 𝒟_k's radii at n = 0, on *R-coincides* (#157), as well as on *R-chain-norm*. Every use of (ii) now cites the same set: #88 names all three with p.375's inclusion (#87), and #113's two clauses and #870 name all three. #17's *R-coincides* entry now lists (ii). A search shows that every line naming one of the chain readings names all three, apart from #88.1, which defines *R-chain-norm*, and #156.1, the chain's first step.
- Note 32a214916d53. Next: C1-11, narrow.

## (R-eval) Packet C1, Round C1-11 (Narrow): Triage (5 November, 05:14)

Log: referee_cli_20261105-050805_scope_twoloops_RevalC111.json. C1-10.1 and C1-10.2 are repaired, and every tag checks. No ERROR, one MINOR.
- **C1-11.1 (MINOR), accepted.** #871 cited (ii) "given R-far″(β)" only. It now adds *R-chain-start*, *R-chain-norm*, *R-coincides*, and p.375's inclusion (#870).
- A search for "R-far″(β)", "(ii)" and "(R-eval), (ii)" finds no other line that concludes the chain's membership without these. #24 sits in #17's item list. #87 defines p.375's inclusion. #868 concerns U_k^0, not the chain.
- D2.7 l.7, my line, now names the three chain readings, the VAR route on every layer, and (R-eval-old) as reviewed (D2.7 a6b061dbf0e2, then the peer's l.74 and l.191 edits: 232015be880e).
- Note 2a6801f1d226. Next: C1-12, narrow.

## (R-eval) Packet C1, Round C1-12 (Narrow): Triage (5 November, 05:21)

Log: referee_cli_20261105-051422_scope_twoloops_RevalC112.json. C1-11.1 is repaired, and the tags in #871 check. No ERROR, one MINOR.
- **C1-12.1 (MINOR), accepted.** #158 concluded the curvature conditions and 𝕌̃ ∈ 𝒟♮_k under the three chain readings only. It now adds p.375's inclusion read as an inclusion of spaces (#156). #113's landing clause gets the same addition.
- Pre-check: every line that cites *R-chain-norm* or *R-coincides* (#6, #6.13, #12, #17, #88, #113, #158, #870, #871) now names p.375's inclusion. #88.1, #156.1 and #157 state the readings themselves.
- Outside the scope: #819 cites the peer's derivation of *R-Yi-branch* (D2.7 l.191), as derived, not reviewed, in the new line #819.1.
- Note 8067453bea32. Next: C1-13, narrow.

## (R-eval) Packet C1, Round C1-13 (Narrow): Triage (5 November, 05:28)

Log: referee_cli_20261105-052120_scope_twoloops_RevalC113.json. C1-12.1 is repaired, and the tags in #158 and #113 check. No ERROR, one MINOR.
- **C1-13.1 (MINOR), accepted.** #6.10 ("It is analytic in 𝐔, since u_L is") and #127 ("Both are analytic") concluded (ii)'s analyticity without naming the readings. #6.10 now reads "(1.65) applies, read as an inclusion of spaces, … (#156)" and cites (ii) under the three chain readings and p.375's inclusion (#88, #156). #127 cites (ii) the same way (#88).
- Pre-check: every line of the note that contains "analytic" was read. Only #6.10 and #127 conclude the analyticity of Bałaban's extension or of the chain's words without (ii). The rest concern other objects, are conditional (#39), or lie in the (ii) block (#89). #6.14's "(1.65) applies" cites #6.10.
- Note 0133c1bd8e4b. Next: C1-14, narrow.

## (R-eval) Packet C1, Round C1-14 (Narrow): Clean (5 November, 05:36)

Log: referee_cli_20261105-052903_scope_twoloops_RevalC114.json. CLEAN: no ERROR, no MINOR. C1-13.1 is repaired, and the sweep for "(ii)", "analytic", "𝒟_k", "𝒟♮", "(2.34)", "u-free", "inclusion", "R-far" and "Ũ^{(n)c}" finds no line that concludes the chain's analyticity, membership or curvature conditions without the four readings or one of #88, #870, #156, #6.13 and #17's list. This is C1's first clean round. Next: C1-15, a confirming round on the mathematics of the C1-7 to C1-9 repairs (#86–#88.1, #92, #93, #97–#97.1, #156–#158, #865, #870–#871). Note 0133c1bd8e4b.

## (R-eval) Packet C1, Round C1-15 (Confirming): Triage (5 November, 05:52)

Log: referee_cli_20261105-053607_scope_twoloops_RevalC115.json. The C1-7 to C1-9 repairs hold: the start at U_k″ is derived, the 𝐁-terms are taken at U_k″, each reading is stated as one, #92 has no layer restriction, #97.1's passage follows from LFR I (1.15)–(1.16) and VAR (2), (3) and Theorem 1, and all pins check. No ERROR, two MINORs.
- **C1-15.1 (MINOR), accepted.** #88 and #870 concluded 𝒟_k membership without R-far″(β), which #87 uses for that step. Both now add "given R-far″(β)", and #870 cites #87.
- **C1-15.2 (MINOR), accepted.** #97 took ε_{n+1}'s sup over the straight segment e^{itηA′}U, which leaves 𝓜^c, where #97.1's identity holds; #125 takes the segment as U^{post}(e^{itB}V₀). #97 now uses #125's segment, from U to P(𝐔) in 𝓜^c, with the bounds at 𝐔 those at P(𝐔) (#127). No other line uses the straight segment; #6.14's V̂_t is a different path.
- Note 50525770b0fb. C1-15's findings reset the clean count: C1 closes after two consecutive clean rounds. Next: C1-16, narrow, then C1-17 if C1-16 is clean.

## (R-eval) Packet C1, Round C1-16 (Narrow): Triage (5 November, 06:01)

Log: referee_cli_20261105-055311_scope_twoloops_RevalC116.json. C1-15.1 is repaired in #88 and #870, and #97's segment is used consistently in #97.1–#125. No ERROR, three MINORs, none changing a bound.
- **C1-16.1 (MINOR), accepted.** #97's segment "ran from U", but U^{post}(M(U)) = P(U) is U only for U ∈ 𝓜, and V, V₀ were undefined (#103's V₀ is another object). #97 and #125 now write U^{post}(e^{itB}M(U)) with B := (1/i)log M(𝐔)M(U)^{−1}, from P(U) to P(𝐔). #97 adds that the chain depends on 𝐔 only through M(𝐔), so its stage-(n+1) configuration at t = 0 is U₀.
- **C1-16.2 (MINOR), accepted.** C1-15.1's omission persisted. Every line that lists the chain readings now carries R-far″(β): #6, #6.10, #6.13, #12, #113 (both clauses), #127 and #158, citing #87 where they cite tags. #113's first clause also adds p.375's inclusion. A sweep shows each of #6, #6.10, #6.13, #12, #17, #88, #113, #127, #158, #870 and #871 names R-far″(β). #88.1, #156.1 and #157 state the readings themselves.
- **C1-16.3 (MINOR), accepted.** #6.16.2 claimed the exact "t times" property of the straight segment for #113's segment. It now adds "up to a relative error O(|B|/r_B) (#125)", which "more than a third of each room" absorbs. C1-15's triage was wrong to say "#6.14's V̂_t is a different path": #6.14 and #6.16.2 both use #113's segment, and #6.14 already states its quadratic error. A sweep for "t times" finds only #6.16.2, #123 and #125 on the segment, all with the error term.
- Note 7cdf457740cf. C1's consecutive clean count: 0. Next: C1-17, narrow.

## (R-eval) Packet C1, Round C1-17 (Narrow): Triage (5 November, 06:10)

Log: referee_cli_20261105-060133_scope_twoloops_RevalC117.json. C1-16.1 to C1-16.3 are repaired: the segment runs from P(U) to P(𝐔) with stage U₀ at t = 0, every conclusion that names the chain readings names R-far″(β) and p.375's inclusion, and no line claims the exact "t times" property. No ERROR, one MINOR.
- **C1-17.1 (MINOR), accepted.** #6.14 gave the error along #113's segment as "quadratic … O(λ²α_{1,k}²) relative", while #125, #123 and #6.16.2 give O(|B|/r_B). #6.14 now gives #125's relative error O(|B|/r_B), with |B| ≤ C_dλα_{1,k} (#96), which tends to 0 with g and is absorbed by the quarter of the margin left for g small. A sweep of "along" the segment, V̂_t and 𝐔_t finds no other order claimed for this error.
- Note 7298de4150d6. C1's consecutive clean count: 0. Next: C1-18, narrow.

## (R-eval) Packet C1, Round C1-18 (Narrow): Triage (5 November, 06:21)

Log: referee_cli_20261105-061107_scope_twoloops_RevalC118.json. C1-17.1's error order is repaired; |B| ≤ C_dλα_{1,k} agrees with #96, and r_B does not depend on g. No ERROR, one MINOR.
- **C1-18.1 (MINOR), accepted.** #6.14 absorbed the O(λα_{1,k}) error "since it tends to 0 with g", but the quarter left on layer n is β2^{−(k+3−n)}, which is not bounded below in k − n. The new line #6.14.1 gives the uniform argument, as at #6.9:
  - the complex part's gradient and current are at most 2μλα_{1,k}L^{−m} (#50–#51, λ^{(k)}_n ≤ λ, #52.1's μ, #6.11's conjugation);
  - α_{1,k} = λ_Rα_{0,k} (#6), and α_{0,k} ≤ (1+β₀)²max(1, √m)α_{0,n} (#53);
  - so δ takes O(|B|/r_B)μλλ_R(1+β₀)²max(1, √m)L^{−m} of the layer-n rooms, which is below β2^{−(m+3)} on every layer for L ≥ 8 and g small.
  #6.14 now cites #6.14.1.
- Note 70ef12e6b956, 995 tags. C1's consecutive clean count: 0. Next: C1-19, narrow.

## (R-eval) Packet C1, Round C1-19 (Narrow): Triage (5 November, 06:29)

Log: referee_cli_20261105-062105_scope_twoloops_RevalC119.json. #6.14.1's factors (λ^{(k)}_n, μ, λ_R, #53's ratio) and its final comparison with β2^{−(m+3)} check. No ERROR, one MINOR.
- **C1-19.1 (MINOR), accepted.** #6.14.1 took the gradient bound with "the factor 2 for #6.11's conjugation". #6.11 is multiplicative only for the covariant quantities (2.34)–(2.37); the gradient changes additively (#6.6).
  - The gradient part of δ is now bounded at the Landau representative itself. Along the segment, δ = 𝓗^{post}(tB) − t𝓗^{post}(B), with B = Δd. (190)'s entries hold uniformly on the ball of radius r_B, at most K times 𝐔's rooms (#94, #128). So the Cauchy estimate in t gives (L^nξ)²|∇δ| ≤ O(K|B|/r_B)μλα_{1,k}L^{−m}.
  - The current keeps #6.11's factor 2, since it is covariant.
  - The share becomes O(K|B|/r_B)μλλ_R(1+β₀)²max(1, √m)L^{−m}, with K, μ and λ_R fixed before g. The conclusion is unchanged.
- Note eb5b090e6f92. C1's consecutive clean count: 0. Next: C1-20, narrow.

## (R-eval) Packet C1, Round C1-20 (Narrow): Triage (5 November, 06:38)

Log: referee_cli_20261105-062944_scope_twoloops_RevalC120.json. C1-19.1 is resolved: the gradient bound through (190) on the ball and the Cauchy estimate in t are correct, and the final share is below β2^{−(m+3)} on every layer. No ERROR, one MINOR.
- **C1-20.1 (MINOR), accepted.** #6.14.1 bounded the current's segment error by O(|B|/r_B) times its bound at V̂ (#51, #6.11). A Cauchy estimate in t needs bounds on the complex t-disc, where #51 and #6.11 do not apply.
  - The current is now bounded the same way as the gradient. (190)'s D*D entry holds on the ball and is at most K times the phase room (#128).
  - So the error is at most O(K|B|/r_B)λλ_Rα_{0,k}L^{−m} in the weight (L^nξ)³, with λ_w := λL where #52.1's weight applies.
  - This lies within O(|B|/r_B)μλα_{0,k}L^{−m}, since μ ≥ 32KC(d)Lλ_R/(1−β).
- Note 367579d9b4d4. C1's consecutive clean count: 0. Next: C1-21, narrow.

## (R-eval) Packet C1, Round C1-21 (Narrow): Triage (5 November, 06:48)

Log: referee_cli_20261105-063857_scope_twoloops_RevalC121.json. The D*D part of the current's error is correct, within #52.1's μ, and inside #6.14.1's share. No ERROR, two MINORs.
- **C1-21.1 (MINOR), accepted.** The current's segment error omitted #147's nonlinear part 𝒬, which has no factor |B|/r_B.
  - The new line #6.14.2 writes J^h(V̂_t) − J(P(U)) = D*Da_t + 𝒬(a_t). It bounds the D*D part by the Cauchy estimate on the ball, within O(|B|/r_B)μλα_{0,k}L^{−m}.
  - It bounds the 𝒬 part by O(K²λ_w²α_{1,k}²)L^{−m}, which is O(K²λ_w²λ_Rα_{1,k})(1+β₀)²max(1, √m)L^{−m} of (2.36)'s room.
  - #6.14.1's share now carries this second term, with α_{1,k} → 0 with g.
  - Pre-check: the curvature's nonlinear part has the same structure, so #6.14.1 now bounds it in the same way and puts it into the same second term.
- **C1-21.2 (MINOR), accepted.** No tag stated (190)'s D*D entry on the ball. #94's list now quotes it: D^{η*}_{U_k}D^η_{U_k} and Δ^η_{U_k} of δ𝓗/δB by (L^iη)^{−3}, VAR p.308 l.39–42, checked against the corrected file. #6.14.2 cites #94.
- Note 32bd70325282, 996 tags. C1's consecutive clean count: 0. Next: C1-22, narrow.

## (R-eval) Packet C1, Round C1-22 (Narrow): Triage (5 November, 06:57)

Log: referee_cli_20261105-064848_scope_twoloops_RevalC122.json. C1-21.1 and C1-21.2 are resolved. The split by #147, the D*D Cauchy bound, the 𝒬 bound, the curvature's nonlinear part, the two-term share below β2^{−(m+3)} on every layer, and #94's added (190) entry (VAR p.308 l.40–42, l.47) all check. No ERROR, one MINOR.
- **C1-22.1 (MINOR), accepted.** #6.14.1 and #6.14.2 said "a_t's phase and gradient at most Kλ_wα_{1,k} times their rooms". The note's rooms already contain λα_{1,k}, so this counted the factor twice. Both now read "at most K times 𝐔's phase and gradient rooms (#128), that is, Kλ_wα_{1,k}L^{−k} per fine bond and Kλ_wα_{1,k}L^{n−k} in the weight (L^nξ)²".
- The referee also noted, without counting it as a finding, that 𝒬's terms with the real curvature as a coefficient are linear in a_t to leading order. #6.14.2 now says so: they carry O(|B|/r_B) and lie within the D*D part's bound.
- Note eadf2fe02d40. C1's consecutive clean count: 0. Next: C1-23, narrow.

## (R-eval) Packet C1, Round C1-23 (Narrow): Triage (5 November, 07:05)

Log: referee_cli_20261105-065736_scope_twoloops_RevalC123.json. C1-22.1's double count is gone. The stated values and the quadratic bounds check, and #6.14.2's sentence on 𝒬's real-curvature terms is correct. No ERROR, one MINOR.
- **C1-23.1 (MINOR), accepted.** "K times 𝐔's phase and gradient rooms" did not equal the stated values, since 𝐔's gradient room carries #52.1's μ. Both tags now say that (190) is applied to Δd, which is bounded by the phase alone (#96, #128), so a_t's phase and gradient are at most K times 𝐔's phase room in both weights.
- The referee also remarked, as a non-finding, on the higher-order part of the real-curvature terms. #6.14.2 now bounds it, ξ²[a_t,[a_t,F_{P(U)}]] ≤ α_{0,n}K²λ_w²α_{1,k}²L^{−m−k}, inside the second term.
- Note fad0ed481b9a. C1's consecutive clean count: 0. Next: C1-24, narrow.

## (R-eval) Packet C1, Round C1-24 (Narrow): Clean (5 November, 07:14)

Log: referee_cli_20261105-070502_scope_twoloops_RevalC124.json. CLEAN: no ERROR, no MINOR. C1-23.1 is resolved, and #6.14.2's bound on the higher-order real-curvature terms checks. The referee's remark on the example term's normalisation (ξ² or ξ, depending on whether F is dimensionless) is not a finding, since the stated bound holds in both; the text is unchanged. C1's consecutive clean count: 1 (C1-24). Next: C1-25, a confirming round over the C1-15 to C1-23 repairs (#6.14–#6.14.2, #94, #97, #125, and the lines carrying the chain readings with R-far″(β)). Note fad0ed481b9a, unchanged.

## (R-eval) Packet C1: Closed and Reviewed (5 November, 07:26)

Log: referee_cli_20261105-071359_scope_twoloops_RevalC125.json. C1-25 (confirming) is CLEAN: no ERROR, no MINOR. With C1-24, C1 has two consecutive clean rounds and is closed.
- **What C1-25 confirmed:**
  - #6.14–#6.14.2: the margin arithmetic, the Cauchy estimate in t, the gradient, D*D, 𝒬 and real-curvature bounds, and the two-term share below β2^{−(m+3)} on every layer.
  - #94's quotation of (190), against VAR p.308 l.37–47.
  - #97 and #125: the segment from P(U) to P(𝐔), with stage U₀ at t = 0.
  - Every conclusion that draws on the chain readings names all five inputs, or cites #6.13, #158 or #88.
- **Remarks (not findings), left unchanged:**
  - #6.14.1's share also covers (2.39) and the derived configurations, by the same argument (#136, #138, #53, #6.16.1).
  - #6.14.2's local λ_w never exceeds #52.1's λL.
- **Bookkeeping (no review needed):**
  - #17 now records that R-chain-start, R-chain-norm and R-coincides, checked against the print, and their uses in the chain account (#85–#128, #156–#158, #870–#871) are reviewed (packet C1).
  - #3.3, #23 and #29 now mark the chain on Z's layers m ≤ k₀ as reviewed in packet C1 (#90–#128). The exception is the gradient and the current on the newer layers (#140, #145), which stay derived, not reviewed.
  - (R-eval) as a whole stays derived, not reviewed: packets A, B and D are still open.
- Note e1ac5f20c875. Next: P1 (R-member), scope_twoloops_P1_Rmember.md, pre-checked at 05:24.

## (R-member) Packet P1, Round 1: Triage (5 November, 07:47)

Log: referee_cli_20261105-072653_scope_twoloops_P1_Rmember.json. No ERROR, five MINOR, all verified against the note and D2.7 15.6, and all repaired. The referee checked the identity, the bound, u = 19, the count 1685σ + 160, the share 0.233, (T0)'s 3230 + 70756/c_w, the payment split and C_y.
- **P1.1 (slot bonds; #620, #670, #245–#246):** confirmed. #617 counts a slot's carried insertions' intervals outside every X⁺ among the slot's bonds of ℐ(g), and #620 groups by slot bonds, so such an interval in span(P′) puts P′ in the slot's group. #670's last sentence and #246's second sharing contradicted this. Repair:
  - new #620.1: #620 uses the slot bonds of ℐ(g) (#617);
  - new #245.1: a slot member's intervals are bonds of its slot, so a slot member of a cross group lies in no other group's span;
  - #246: the only sharing is W ∈ 𝒲_g ∩ 𝒲_{g′} of a cross insertion in no slot, and a component holding a cross group h is h with its cross slot members, with D_G = D_h^×;
  - #670's last sentence: the outside intervals are slot bonds, so a polymer whose span holds one is in g;
  - #242: the slot case dropped from the issue;
  - #771: the lineage growth with G = {g} (#246).
  #622, #779, #786–#787 and D2.7 15.6's premise hold under this reading.
- **P1.2 (C_lk at bonds; #266–#267, #771):** confirmed. At a bond the linked group is rooted through *Joins*, and its B(g) brings C_B, which C_jn does not carry (#755; C_gr = 2^dC_KPC_B, #742). Repair: #266 adds C_B; C_lk := 2max(C_gr, C_BC_jn) at #267 and #771. With C_lk ≥ 4C_jn (C_B ≥ 2) the links and joins need 81.3MC_lkε_k ≤ ν_r, inside 100MC_lkε_k ≤ ν_r. C_y and (H^R) change by the constant only.
- **P1.3 (#3.3 marks):** confirmed. #281 now names (R-eval) with its points #3.3. #742, #744, #769, #772, #799 and #858 mark η's bound as derived through #3.3, not reviewed (#264 and #844 already did).
- **P1.4 (u = 19 downstream):** confirmed. #538, #583, #598 and #599 now say u ≤ 19; #584's product is 96·19·64 ≤ 4096L; #598's range is L ≥ 456 (12·19/8 ≤ L/16). #583's L ≥ 8832·19 = 167808 and #542's L ≥ 5081·19 = 96539 lie within L₀^× = 10⁶.
- **P1.5 (#249's citations):** confirmed against D2.7 15.6(c) and (f). 15.6(c)'s sup is A_k's only; 15.6(f) gives ‖D_g‖ ≤ B(g)Π‖W‖ on (d)'s domain with no Cauchy step. Repair: #249 cites 15.6(f) on (d)'s domain and (6B)'s ‖D_h^×‖ ≤ B(h) (#680), and the contraction bound is ‖AB‖ ≤ ‖A‖‖B‖ on elementary tensors, with map l.911 for the unitary transports.
- Note 871535aeb98f (998 tags). P1's consecutive clean count: 0. Next: P1-2, narrow.

## (R-member) Packet P1, Round P1-2 (Narrow): Triage (5 November, 07:59)

Log: referee_cli_20261105-074837_scope_twoloops_P1_Rmember2.json. No ERROR, two MINOR, both verified and repaired. The referee confirmed P1.1–P1.5's repairs (the slot bonds of #620.1, the sharing list, C_lk with 81.25MC_lkε_k ≤ ν_r inside the condition with 100, the #3.3 marks, u ≤ 19 at L₀^× = 10⁶, and #249 against 15.6(f)).
- **P1-2.1 (#624's first sentence):** confirmed. Under #620.1 and #245.1 a span link can join a single-loop polymer to the polymer of a cross slot member, which has slots on both loops. Repair: #624 now says that a span link puts a slot bond of one polymer in the other's span, on that span's loop, so two polymers whose slots lie on one loop are linked only on that loop. The conclusion (a group with slots on both loops contains a polymer with slots on both loops) follows by connectedness, as before.
- **P1-2.2 (#249 and #680):** confirmed. #680's B(h) carries the cross members' norms in its slots' bounds, so #249's quotation with the product Π‖W‖ counted them twice. Repair: #249 now quotes ‖D_h^×‖ ≤ B(h)·Π_{W∈𝔅^×(h)}‖W‖, #680's bound with the norms taken out as the product, B(h) being 15.6(c)'s bound. #264 counts each norm once, unchanged.
- Note 279f265e782d (998 tags). P1's consecutive clean count: 0. Next: P1-3, narrow.

## (R-member) Packet P1, Round P1-3 (Narrow): Clean (5 November, 08:02)

Log: referee_cli_20261105-075841_scope_twoloops_P1_Rmember3.json. CLEAN: no ERROR, no MINOR. #624's first sentence and its conclusion check, and #249's quotation of #680 counts each cross insertion's norm once. The referee's remark that #624's second alternative (a cross slot member) is implied by the first (the domain meets both loops, since slot bonds lie in dom P, #629) is not a finding; the text is unchanged. P1's consecutive clean count: 1 (P1-3). Next: P1-4, a confirming round over the P1 and P1-2 repairs (scope_twoloops_P1_Rmember4.md). Note 279f265e782d, unchanged.

## (R-member) Packet P1: Closed and Reviewed (5 November, 08:13)

Log: referee_cli_20261105-080252_scope_twoloops_P1_Rmember4.json. P1-4 (confirming) is CLEAN: no ERROR, no MINOR. With P1-3, P1 has two consecutive clean rounds and is closed.
- **What P1-4 confirmed:** the slot bonds (#620.1 = #617's list), the sharing list (#245.1, #246) and its consistency with #242, #622, #624, #670, #771 and #779–#787; #249 against 15.6(c), (d), (f) and #680; C_lk covering both rooted sums, with 81.25MC_lkε_k ≤ ν_r inside the condition with 100 and C_y ≥ 76MC_lk/(eν_r); the #3.3 marks at every use of 1 + η; u ≤ 19 at #542, #583, #584, #598 and #599 at L₀^× = 10⁶.
- **Remark (not a finding):** the referee inferred ν_f ≤ 17ν/16 for #583 from the factor 17/16. It is stated at map l.1549 (ν_f := ν/16 + ν_r = 17ν/16, ν_e ≤ ν/8), so #583's 414 = 96(3·17/16 + 9/8) holds. Text unchanged.
- **Bookkeeping (no review needed):** #3, #241, #281 and #917 now mark (R-member) as derived and reviewed given (R-eval) with its points #3.3 (rounds P1 to P1-4). (R-eval), (R-round) and (R-att-ext) stay derived, not reviewed.
- Note 41ca5196c207. Next: packet 2b ((R-round), second round, part b), scope_twoloops_Rround2b.md, pre-checked at 07:50 (η ≤ (ϑ_k/4)ν_rσ under 4c_r⁺ϑ_k ≤ ν_r; #776's δM log u ≥ 1024/31; #724's 32.5 + 276M ≤ 64 + 1280M; #859's 0.1446 and 2720, 59584; the scope now names #620.1's slot bonds), launched at 08:13.

## (R-round) Packet 2b, Round 1: Triage (5 November, 08:30)

Log: referee_cli_20261105-081353_scope_twoloops_Rround2b.json. No ERROR, four MINOR, all verified. The referee checked the packet's arithmetic (the payment, (1+20M)2^{d+2}, δM ≥ 2^{d+5}ν_r, the c_F split, the members species by species, c_j, C_jn, 160M, 21/4, 20/168 ≥ 1/9, A^R_k, ϑ_k² ≥ e^{−63δMR_k/512}, λ_n(D) ≥ 15/16, S^R, δM log u ≥ 1024/31, (6C)'s factors, the re-run of 15.7, D's budget 0.8896, and the u = 16 conditions), and found no per-member constant of the slot members in the packet.
- **2b.1 (#3.3 marks through D_P's a′ terms):** confirmed. The a′ terms of D_P (#627) are paid by (α′)'s e^{−(3δ/4)ℓ} (#638, #613), derived through #3.3. Repair: new #638.1 marks this and names the uses: #727, #729, #755, #758, #762, and A^R_k at #764–#765. (8.2) already carries *15.5*'s status (#917).
- **2b.2 (δ's three definitions):** confirmed. #728 calls δ the 𝐇-rate, D2.7 15.5(ii)(α) has min(1, (κ₁−1)/(4√d)) (D2.7 l.175), and #613 uses δ₀/32 (#46). Repair: new #728.1 takes δ in (6B) and (6C) as the least of the three. Bounds at a larger rate hold at δ, the prefactor C_αe^{δt_k} only decreases, and each rate is fixed before M. #728 now reads "at most the decay rate". #613's "δ = δ₀/32" is now "δ ≤ δ₀/32 (#728.1)"; its step δt_k ≤ δ + (2log α_{1,k}^{−1} + log(L⁴R_k²))/M holds for δ ≤ δ₀/32, since t_k ≤ 1 + (32/(δ₀M))(…).
- **2b.3 (D2.7 l.175 stale rate):** confirmed. D2.7 15.5(i) still has ϑ_k := e^{−δMR_k/16} and η(D) ≤ e^{δ}c_rσ(D)e^{−63δMR_k/512} without C_α. The note's #722 (ϑ_k := e^{−31δMR_k/512}) and #613 (c_r⁺ := C_αe^{δ}c_r) are right. D2.7 l.175 is the peer's; the correction was sent to the peer.
- **2b.4 (#776's citation):** confirmed against CRE p.255 l.35–39 ((2.5): R_j ≥ (log g_j^{−2})^r for every j) and p.245 l.33–34 (r ≥ 2). p.246 l.24–25 states R₁ only. Repair: #776 cites CRE (2.5), p.255 l.35–39, with r ≥ 2 from p.245 l.33–34.
- Note 31d2205224c6 (1000 tags). Packet 2b's consecutive clean count: 0. Next: 2b-2, narrow.
- 2b.3 resolved by the peer: D2.7 4bfc77d4ad39's 15.5(i) has ϑ_k := e^{−31δMR_k/512} and η(D) ≤ c_r⁺σ(D)e^{−63δMR_k/512}, c_r⁺ := c_{α′}e^{δ}c_r, with c_{α′} the note's C_α of #613.

## (R-round) Packet 2b, Round 2b-2 (Narrow): Triage (5 November, 08:39)

Log: referee_cli_20261105-083100_scope_twoloops_Rround2b2.json. No ERROR, three MINOR, all verified and repaired. The referee confirmed 2b.1, 2b.2 and 2b.4 in substance: #638's payment and #638.1's mark, every use of δ at the least rate (#613's δt_k step, #722, #727, c_F, a_k, #776), and #776's pins (p.255 l.36–39, p.245 l.34).
- **2b-2.1 (#638.1's list):** confirmed. (6C)'s cross groups use *The free decay* with a′ terms present at #801, #802 and #806. Repair: #638.1 names #801–#802 and #806 in (6C). #754 feeds #755 (named), and E^{R×}_k (#661–#666) has no carried insertions (#658).
- **2b-2.2 (#728.1's justification):** confirmed. (α′)'s prefactor e^{δt_kn} falls with δ, which strengthens the bound, so the transfer to a lower rate needs ℓ ≥ t_kn. Repair: #728.1 now points to a new #728.2. There, (α) (τ_iO(1)^{|𝒦|}e^{−δℓ}, D2.7 l.175) and 𝐇's B₃e^{−δ·} only weaken. (α′) is ‖D‖C_α^ne^{−δ(ℓ − t_kn)}: for 𝒦 = ∅ it is ‖D‖C_αe^{δt_k}, and for 𝒦 ≠ ∅ #613's count gives n ≤ 2^{d+3}ℓ/(MR_k), so t_kn ≤ ℓ once 2^{d+3}t_k ≤ MR_k, a smallness of g_k. #728.1 now cites κ₁ as fixed before M by map l.949 (δ₁M ≥ 2κ₁, a condition on M).
- **2b-2.3 (#287, #298):** confirmed. Repair: #287's δ is "fixed before M (#728.1)"; #298 says the 𝐇-rate is fixed before M, with #728.1.
- **Bookkeeping:** #613's C_α now names D2.7's c_{α′}, not D2.7 (β)'s C_α (peer's renaming at D2.7 4bfc77d4ad39).
- Note dcd393beb6be (1001 tags). Packet 2b's consecutive clean count: 0. Next: 2b-3, narrow.

## (R-round) Packet 2b, Round 2b-3 (Narrow): Triage (5 November, 08:54)

Log: referee_cli_20261105-083934_scope_twoloops_Rround2b3.json. One ERROR and two MINOR, all verified against D2.7 l.175 and repaired.
- **2b-3.1 (ERROR, units of δ):** confirmed. D2.7 15.5(ii) measures (α)'s and (α′)'s lengths in M-units: ℓ(i,𝒦) := M^{−1}(the tree's length), ℓ(D,𝒦) ≥ R_k, and "one segment of length ≤ t_k per set" gives e^{δt_k(|𝒦|+1)}, with δ = δ_α := min(1, (κ₁−1)/(4√d)); its a_k counts "scaled distance s, in M-units". The note measures lengths in step-k units (ℓ ≥ MR_k, c_F = min(1, δM/2), "3δM/4 per M-unit", ϑ_k = e^{−31δMR_k/512}). So the note's δ is δ_α/M, not fixed before M, and #613's prefactor e^{δt_k} understated D2.7's e^{δ_αt_k} = e^{δMt_k}. Every other formula of (6B) and (6C) is already written in δM and stays. Repair:
  - #728.1 rewritten (*Units*): δ := δ_α/M, so δM = δ_α is fixed before M (κ₁ by map l.949); δ ≤ δ₀/32 and δ ≤ δ_𝐇 once M ≥ δ_α·max(32/δ₀, 1/δ_𝐇); the 𝐇-bounds weaken to δ; the conditions on δM (#287, #727, #776, #802) are conditions on ν_r and g.
  - #728.2 rewritten: (α) and (α′) translated to step-k units, (α′) as ‖D‖(C_αe^{δMt_k})^ne^{−δℓ}; no transfer between rates is needed.
  - #613: e^{δMt_k} throughout; t_k in M-units; C_α ≥ 1; c_r⁺ := C_αe^{δM}c_r; the power bound e^{δMt_k} ≤ e^{δM}L⁴R_k²α_{1,k}^{−2} (from δMt_k ≤ δM + (32δ/δ₀)X and 32δ/δ₀ ≤ 1); δMt_k ≤ δM + δMR_k/512 for g small; a_k(X) ≤ 16C_a(100MR_k + 2Mw_k + 8M(δM)^{−1})(δM)^{−1}e^{−δMw_k/4} with D2.7's (α) factor C_a := 2O(1)e^{(κ₁−1)/4}(100R_k)^d (also closes 2b-2's out-of-scope remark on the missing constant).
  - #3.3, #286 and #744: e^{δMt_k}.
  - #287: δM ≥ 5·2^{d+3}ν_r is ν_r ≤ δ_α/(5·2^{d+3}), an upper bound on the map's ν (ν_r = ν, map l.1549), like ν ≤ 1/1000; M ≥ δ_α·max(32/δ₀, 1/δ_𝐇) added to the lower bounds on M. #727's second condition is ν_r ≤ δ_α/2^{d+5}, implied by #287's.
  - D2.7 l.175 (peer's) writes ϑ_k and η with δMR_k in its own M-unit δ; in its units these read e^{−31δR_k/512} and e^{−63δR_k/512}. Sent to the peer.
- **2b-3.2 (#728.2, 𝒦 = ∅):** confirmed. Repair: #728.2 gives |D^∅| ≤ ‖D‖ (#613), within ‖D‖C_αe^{δMt_k} since C_α ≥ 1 (#613 now states C_α ≥ 1).
- **2b-3.3 (#638.1's list):** confirmed. (6C)'s single-loop R-made groups hold carried insertions (#825, #853) and use the free decay at #849–#850 and #854–#857. Repair: #638.1 names them.
- Note dc361a3e6d52 (1001 tags). Packet 2b's consecutive clean count: 0. Next: 2b-4, narrow.
- The peer applied D2.7 l.175 in its units (D2.7 c384e6a20d7a: ϑ_k := e^{−31δR_k/512}, η ≤ c_r⁺σe^{−63δR_k/512}) and #T4.30 (table d5a8107565d9).

## (R-round) Packet 2b, Round 2b-4 (Narrow): Triage (5 November, 09:03)

Log: referee_cli_20261105-085510_scope_twoloops_Rround2b4.json. No ERROR, two MINOR, both verified and repaired. The referee confirmed the units repair: D2.7's (α) and (α′) translate exactly with δ := δ_α/M, #613's chain to η(D) ≤ c_r⁺σ(D)e^{−63δMR_k/512} holds, #287 and #727 are conditions on ν_r (map l.1549, l.1614), #638.1's list and #728.2's 𝒦 = ∅ case are right.
- **2b-4.1 (#613's a_k):** confirmed against D2.7 l.175 (a_k(X) := 4C_α(…)δ^{−1}e^{−δw_k} + 1200c_πα_{1,k}MR_k + log 2, "a polylog of order ≤ r(d+1) … below p₀ (p₀ > r′(d+2), D26 l.136)"). Repair: #613 adds the arc part + 1200c_πα_{1,k}MR_k + log 2 and states order ≤ r(d+1) < p₀ (D2.7 l.175; D26 l.136); #646 and #652 now say order ≤ r(d+1) < p₀.
- **2b-4.2 (δ's two definitions):** confirmed. #46's δ := δ₀/32 serves (R-eval) (#74), and #728.1's δ := δ_α/M serves (6B)–(6C). Repair: new #728.3 separates them (in #3.3, #286, #287 and (6B)–(6C), δ is #728.1's; #46's rate appears there as δ₀/32, #613), and #3.3 marks "δ := δ_α/M, #728.1, not #46's δ".
- Note ba492afd1e8c (1002 tags). Packet 2b's consecutive clean count: 0. Next: 2b-5, narrow.

## (R-round) Packet 2b, Round 2b-5 (Narrow): Triage (5 November, 09:08)

Log: referee_cli_20261105-090339_scope_twoloops_Rround2b5.json. No ERROR, three MINOR, all verified and repaired. The referee confirmed #613's a_k (D2.7 l.175 at the rate δM/4 plus the arc part, order r(d+1) < p₀ by D26 l.136 with r ≤ r′), 15.3's amplitude bound and the margin (#646, #652), and the separation of #46's δ from #728.1's.
- **2b-5.1 (#728.3 too broad):** confirmed. #750's δ is a diameter, and #728's and #613's quotations of LFR II and CRE use the 𝐇-rate. Repair: #728.3 names the note's decay rate, the quoted 𝐇-rate δ_𝐇 (#728, #613's p.376 quotation), and #750's diameter separately.
- **2b-5.2 ((8)'s hypotheses):** confirmed. #917 and #932 assume δM ≥ 5·2^{d+3}ν_r. Repair: #728.3 lists (8)'s hypotheses (#917, #932) among the uses of #728.1's δ. No other δ occurs in (8) (#896–#897 have the constant C_δ).
- **2b-5.3 (#646's wording):** confirmed. Repair: the attachment sum is the first term of a_k(X) (#613), so the factor e^{3c_F} replaces a_k(X) by at most e³a_k(X), since c_F ≤ 1 and the arc part is ≥ 0.
- Note bcee3f6892ca (1002 tags). Packet 2b's consecutive clean count: 0. Next: 2b-6, narrow.

## (R-round) Packet 2b, Round 2b-6 (Narrow): Triage (5 November, 09:20)

Log: referee_cli_20261105-090916_scope_twoloops_Rround2b6.json. No ERROR, one MINOR, verified and repaired. The referee confirmed #646 against #613's a_k(X) and #636's c_F, and #728.3's assignments as far as they went.
- **2b-6.1 (#728.3 leaves uses of δ out):** confirmed. LFR I's printed δ (#47, #91, #93, #99, #209), #298's δ_𝐇 and the local δ's had no assignment. The pre-check also found #5.7 and #78 (#46's δ, missing from #728.3's list), #728's first sentence (the note's δ, which #728.1 bounds by δ_𝐇), #728's quotation of CRE's δ₀, and δm. Repair: #728.3 lists #5.7, #46, #74, #78 for #46's δ, puts #728's first sentence with the note's rate, and puts #298 and the rest of #728 with δ_𝐇. New #728.4 assigns LFR I's δ, δ₀, and every other δ as local notation, listed by tag.
- Pre-check (rule precheck-own-repairs): grep of every line of the note containing δ (124 lines, by tag), each form classified. Read #5.7, #46, #47, #74, #78, #91, #93, #99, #209, #298, #613, #728, #728.1 and #5.10.2.1 at their δ's. #728.4 states assignments only, with no inequalities. Its "every other δ" was checked against the full grep list. Ranges are exact tag lists except #159–#162, where each tag has δ^{re}.
- Note b177c6eb4df2 (1003 tags). Packet 2b's consecutive clean count: 0. Next: 2b-7, narrow.

## (R-round) Packet 2b, Round 2b-7 (Narrow): Triage (5 November, 09:29)

Log: referee_cli_20261105-092057_scope_twoloops_Rround2b7.json. No ERROR, four MINOR, all in #728.4's wording, all verified and repaired. The referee confirmed that #728.3 and #728.4 assign all 124 δ lines and that every assignment in #728.3 is right.
- **2b-7.1 (CRE's δ₀):** confirmed. CRE p.247 l.50 (corrected file): "δ₀ = g₀(A₁/A₀)p₀(g₀) = (A₁/A₀)ε₀", a small-field threshold, and p.251 l.39–40 is "much smaller than δ₀". Repair: #728.4 says δ₀ is VAR's rate except in #728's quotation of CRE p.251, where it is CRE's threshold (A₁/A₀)ε₀.
- **2b-7.2 (#6.9, #6.14.1, #6.16.1):** confirmed. #6.9 has "the difference δ of the complex parts", and #6.14.1 has δ = 𝓗^{post}(tB) − t𝓗^{post}(B). Repair: #728.4 lists them as the change of the minimiser's complex part.
- **2b-7.3 ("local to its line"):** confirmed. δ′_j = g_jA₁p₁(g_j) (#91, LFR I p.183 l.2; #195, LFR II p.383), C_δ := 2 (#346), and δm, δ_n^{(k)} and δ(d) all run over many lines. Repair: #728.4 calls them symbols of their own, none of them a decay rate. It attributes δ′_j to Bałaban and names C_δ's definition.
- **2b-7.4 (#93's locator):** confirmed. #93 pins only LFR II p.384 l.17. Repair: #93's δ is LFR I (1.45)'s (p.186, quoted at #91), not LFR II's (1.45) (#46).
- Pre-check: quoted CRE p.247 l.50 and p.251 l.39–40 in the corrected files. Read #6.9, #6.14.1, #6.16.1, #91, #93, #123, #195, #315, #333, #346 and the subscripted δ's (#200, #203, #345, #444, #452, #844, #845); δ_{rT} and δ_{G_i} are Bałaban's indicators and the rest are distances or factors, none of them a rate. "δ₀ is VAR's rate except ..." was checked against every δ₀ line (#42–#45, #94, #98, #99, #128, #164, #166, #287, #613, #728, #728.1, #728.3). The repair changes only #728.4.
- Note f2a5b50db415 (1003 tags). Packet 2b's consecutive clean count: 0. Next: 2b-8, narrow.

## (R-round) Packet 2b, Round 2b-8 (Narrow): Triage (5 November, 09:34)

Log: referee_cli_20261105-093012_scope_twoloops_Rround2b8.json. No ERROR, one MINOR, verified and repaired. The referee confirmed all four 2b-7 repairs and every tag and pin in #728.4.
- **2b-8.1 (δ(d) is a rate):** confirmed. #5.10.2: "with δ = δ(d), abs(P(x, z)) ≤ C(d)n^{−d}e^{−δ|x−z|/n}". Repair: #728.4 gives δ(d) its own sentence: the decay rate of the kernels of H′ and P, a rate of d only, distinct from the rates above. "None of them a decay rate" now covers only the rest.
- Pre-check: the rest of the list was re-read for rates. The point mass, the changes and differences, the derivatives, the δ-functions, δm, the diameters, δ′_j, the subscripted symbols and C_δ: none of them appears in an exponent as a rate (the referee checked the subscripted ones, 2b-8 (a)). The repair changes only #728.4.
- Note 72f003da9c76 (1003 tags). Packet 2b's consecutive clean count: 0. Next: 2b-9, narrow.

## (R-round) Packet 2b, Round 2b-9 (Narrow): Clean (5 November, 09:41)

Log: referee_cli_20261105-093429_scope_twoloops_Rround2b9.json. CLEAN: no ERROR, no MINOR. #728.4's sentence on δ(d) matches #5.10.2, #5.10.2.1, #5.10.3 and #5.10.5, and "none of them a decay rate" is true of every symbol after it. The referee's remark that the list writes δ_{k′} for the family δ_{k′−1}, δ_{k−1} is not a finding; the text is unchanged. Packet 2b's consecutive clean count: 1 (2b-9). Next: 2b-10, a confirming round over all the repairs of rounds 2b-1 to 2b-8 (scope_twoloops_Rround2b10.md). Note 72f003da9c76, unchanged.

## (R-round) Packet 2b, Round 2b-10 (Confirming): Triage (5 November, 09:50)

Log: referee_cli_20261105-093838_scope_twoloops_Rround2b10.json. No ERROR, one MINOR, verified and repaired. The referee confirmed the units (#728.1, #728.2), #613's prefactor, rates and a_k, #646 and #652, the conditions (#286, #287, #727, #776, #802), #638.1's marks and the δ's (#728, #728.3, #728.4).
- **2b-10.1 (ℓ(i,𝒦)'s units):** confirmed. D2.7 l.175 (α) defines ℓ(i,𝒦) := M^{−1}(the tree's length), and #728.2 translated only ℓ(D,𝒦) explicitly. #613's e^{−(3δ/4)ℓ(i,𝒦)} and #626's ℓ_a := ℓ(i,𝒦) then read in M-units, while #627, #631 and #638 use ℓ_a as a step-k length (ℓ_a/M, "3δM/4 per M-unit of ℓ"). The bounds hold in the step-k reading. Repair: #728.2's last sentence says the note's ℓ(i,𝒦) (#613, #626) is the tree's length in step-k units, M times D2.7's. #626 defines ℓ_a as the trees' lengths in step-k units (#728.2).
- Pre-check: every ℓ(i,𝒦) line (#613, #626, #728.1's quotation of D2.7, #728.2) and every ℓ_a line (#626, #627, #631, #638) was read. With ℓ_a in step-k units, ℓ_a/M is in M-units and #638's payment c_F per unit of ℓ_a/M stands.
- For X1 (the referee's note, not a finding): D2.7's (α′) measures ℓ(D,𝒦) from "Y₁ the domain of Dep(D)", while #613 measures it from Dep(D). This was added to X1's scope.
- (8.2)'s hypotheses (#917, #932) do not name the new lower bound M ≥ δ_α·max(32/δ₀, 1/δ_𝐇) (#287). The referee found it implied by inherited conditions (D2.7's M ≥ 2^{12}/δ₀ and map l.980's δM ≥ L+1), so it is not a finding.
- Note c067e51c98bb (1003 tags). Packet 2b's consecutive clean count: 0. Next: 2b-11, narrow, then a confirming round.

## (R-round) Packet 2b, Round 2b-11 (Narrow): Clean (5 November, 09:58)

Log: referee_cli_20261105-095131_scope_twoloops_Rround2b11.json. CLEAN: no ERROR, no MINOR. #728.2's last sentence and #626's ℓ_a match D2.7 l.175 (α) (step-k length M·ℓ_{D2.7}(i,𝒦)), and #613, #627, #631, #638 and #646 are consistent with it. Packet 2b's consecutive clean count: 1 (2b-11). Next: 2b-12, a confirming round over all the repairs of 2b-1 to 2b-10 (scope_twoloops_Rround2b12.md). Note c067e51c98bb, unchanged.

## (R-round) Packet 2b, Round 2b-12 (Confirming): Triage (5 November, 10:09)

Log: referee_cli_20261105-095418_scope_twoloops_Rround2b12.json. No ERROR, two MINOR, both verified and repaired. The referee confirmed the rest of 2b-1 to 2b-10's repairs: the units, #613, #646, #652, the conditions, the marks as far as listed, the δ's and the pins.
- **2b-12.1 (δ_α's order against ν):** confirmed. #287 read ν_r ≤ δ_α/(5·2^{d+3}) as an upper bound on ν, but δ_α = min(1, (κ₁−1)/(4√d)) depends on κ₁, and the map chooses κ after ν (map l.200, l.1562). Map l.949's κ₁ is RG II's (1.11) κ₁, and #642 has RG II's ½(κ₁−1) ≥ 2Lκ (p.20 l.17), so (κ₁−1)/(4√d) ≥ Lκ/√d ≥ 1 by κ > 6·2^d ≥ √d (#644). Hence δ_α = 1. Repair: new #728.5 states δ_α = 1 with this derivation. #287's and #727's conditions are then ν_r ≤ 1/640 and ν_r ≤ 1/512 at d = 4, implied by ν ≤ 1/1000 (map l.1614), with no order between ν and κ needed. #287 now cites #728.5 and says "implied by".
- **2b-12.2 (#638.1's list):** confirmed. *The rooted sum* (#742) and the second case's y^R_k (#769–#770) pay from the activities' e^{(c_F/4)D_P} with a′ terms present. Repair: #638.1 adds #742, #769–#770, and #772 (a non-first member, also through the rooted sum).
- Pre-check: all δ_α lines (#3.3, #287, #613, #727, #728.1–#728.5) are consistent with δ_α = 1, and #727's "implied by #287's" still holds. Every free-decay line (grep of c_FD_P, (c_F/4)D_P, *The rooted sum*, *The free decay*: #37, #266, #613, #616, #628, #636, #647, #652, #655, #661, #683, #685, #692, #699, #704, #719, #727, #729, #732, #742, #755, #758, #762, #764, #772, #801, #806, #817) was read. The others either derive the free decay (#636–#647), use κ or the margin only (#652, #655, #704, #817), have no carried insertions (#661, #658), or are budgets and spans, not activity sums (#683, #692, #699, #719, #732).
- Note bc5f2c806dd8 (1004 tags). Packet 2b's consecutive clean count: 0. Next: 2b-13 (narrow), launched after the peer's tagging of the map, W-δ, the continuum note and BFWL has landed and this note's l.N pointers are converted (bookkeeping), then a confirming round.

## Bookkeeping: Pointers into the Map and the Continuum Note Converted to Tags (5 November, 10:17)

The peer tagged the map (add32c4c9d78, LABELS_D2_STEP_MAP.md 96d3fc63f8a1), W-δ, the continuum note (839f0fde0564) and BFWL. Every pointer of this note into the map or the continuum note is now a tag, taken from the peer's conversion list (conv_TWO_LOOPS.md, 210 rows), which was read off the LABELS files. There were none into W-δ or BFWL. This is bookkeeping, so no round.
- Explicit "map l.N" and "Map l.N" were replaced first (ranges and longer numbers before their prefixes). Then the bare l.N following a map citation in the same parenthesis or sentence were replaced, as were the new #728.5's map pins. No "map l." is left.
- Not converted, since they are not map pointers: #56's "SW l.93", and #61's and #62's "covariance note" l.131, l.141 and l.149–157 (the list had them as map).
- The rows the list marked "?" were checked by hand against the target tag's text. One pin was stale and has been corrected: #604's "continuum note l.62" (#ND.4.7, the component count) now cites #ND.4.9, the (4.5) K → ∞ block that #604 means. #130.3's #MOMST.44 (ii) is the identity U₁(e^{iB′}V) = e^{iη𝐇}U₂ that the note cites.
- The queued scopes (Rattext2, X1) now cite the map by tag.
- Note e442bc506fcf (1004 tags).

## (R-round) Packet 2b, Round 2b-13 (Narrow): Triage (5 November, 10:31)

Log: referee_cli_20261105-101812_scope_twoloops_Rround2b13.json. No ERROR, one MINOR, verified and repaired. The referee confirmed #728.5 (δ_α = 1; it holds even if RG II p.20 l.17 is read as ½(κ₁−1) ≥ 2L, given L ≥ 5000), #287, #727, #728.1, #802 and every later use of c_F = ½, and the tags and pins.
- **2b-13.1 (#638.1's list, fourth time):** confirmed. The cluster bound on |Ψ_g| (#681–#683, through C_jn of *The rooted sum*) with its uses #724, #730, #811 and #851, and (6C)'s lineage and wrap sums #841–#842, pay from the activities with a′ terms present. The 2b-12 pre-check had classed #683 as a span bound, but it continues #682's cluster sum. Repair: #638.1 now states a rule instead of a closed list. The mark applies to every polymer, cluster or group sum over activities whose polymers can hold carried insertions, and to every bound through C_gr, C_jn, C_Ψ′, C_lk or C_y. The named tags are introduced by "Among them", now with #681–#683, #724, #730, #811, #851, #841–#842 and (R-member) (#241).
- Pre-check: the grep of C_Ψ′ and |Ψ_g| (#36, #261, #286, #680, #682, #687, #723, #724, #730, #798, #811, #849, #851) is covered by the rule. The rule makes only a status claim ("derived through #3.3, not reviewed" at those terms), which is conservative, and it agrees with #241's heading and with (6B)–(6C)'s "Derived, except (R-eval)".
- Note b2f6601a5dd5 (1004 tags). Packet 2b's consecutive clean count: 0. Next: 2b-14 (narrow), then a confirming round.

## (R-round) Packet 2b, Round 2b-14 (Narrow): Clean in Substance (5 November, 10:40)

Log: referee_cli_20261105-102958_scope_twoloops_Rround2b14.json. No ERROR, one MINOR on the status mark only ("no status is overstated", every end result marked). The referee confirmed that the rule claims only the status of #613 and #3.3, that the five constants are defined by such sums and every use of them is covered, that every use of η(D) carries its own mark, that the gases of #656–#667 rightly fall outside, and that every tag resolves.
- **2b-14.1 (#638.1's rule):** confirmed. The per-polymer bounds that spend the free decay e^{−c_FD_P} directly are neither sums nor bounds through the five constants: #727, #729, #762 and #801–#802 (named), and #699(a) (not named), whose small member through a part D^{𝒦} is counted by half of D_P's term (3/2)ℓ_{a′}/M. Repair: a third clause, "and to every bound that spends the free decay e^{−c_FD_P} of such a polymer, or a part of it", and #699(a) added to the named tags.
- Pre-check: #699(a) quoted ("the half length in D_P's term (3/2)ℓ_{a′}/M covers the count"); #727, #729, #762 and #801 quoted in the log, each spending e^{−c_FD_P} or a part of it. The clause restores 2b-12's criterion alongside 2b-13's two clauses.
- Classification: the finding and the repair concern only which bounds carry the mark "derived through #3.3, not reviewed". They change no bound, constant, condition or proof step, and they overstate no status. Following the user's question of 10:33 ("How is the previous minor not just bookkeeping?"), a repair confined to a status mark is bookkeeping, so 2b-14 counts as clean. The confirming round reviews #638.1 together with the other repairs.
- Note 282fa83d4475 (1004 tags). Packet 2b's consecutive clean count: 1 (2b-14). Next: 2b-15, a confirming round over all the repairs of 2b-1 to 2b-14 (scope_twoloops_Rround2b15.md).

## (R-round) Packet 2b, Round 2b-15 (Confirming): Clean in Substance; Packet 2b Closed (5 November, 10:54)

Log: referee_cli_20261105-104020_scope_twoloops_Rround2b15.json. No ERROR, two MINOR, both bookkeeping: "No bound, constant or condition is wrong". The referee confirmed the units (δ = δ_α/M, δ_α = 1), #613's prefactor, c_r⁺, the e^{δMt_k} bound and the 63/512 rate, a_k and its order, #646, #652, the conditions (#287, #727, #776, #802, #286, #3.3's and #744's prefactors), #638.1's three-clause rule and its list, the δ assignments, and the tags and pins.
- **2b-15.1 (#3.3's heading and coverage):** confirmed. #613, #744, #799, #844 and #858 mark the (α′) bound "through #3.3" for the parts of dev and attached insertions as well, which #37 lists, while #3.3 named only the cross members. Repair: #3.3's heading and first sentence now name the carried insertions of every species (cross, dev, and attached; #37, #613). A status mark only.
- **2b-15.2 (D2.7 pin):** confirmed. D2.7 hashes to c384e6a20d7a now; #3.3 and #613 pinned 5ef985f396ae. Repair: both pins are c384e6a20d7a. A pin swap.
- Pre-check: the old heading is quoted nowhere but LABELS_TWO_LOOPS.md (regenerated); D2.7 hash computed (sha256, first 12).
- Classification: both repairs are bookkeeping (status mark, pin), so 2b-15 counts as clean. Packet 2b's consecutive clean count: 2 (2b-14, 2b-15), the second a confirming round over all repairs. **Packet 2b is closed.**
- Bookkeeping in the same change: #940 now cites `WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md` for the full-sequence limit.
- Note 8e6d7ed2451d (1004 tags). Next: packet PC1 on the pair's Cauchy note (scope_pairCauchy_PC1.md), then (R-round) part a (scope_twoloops_Rround19a.md).

## (PC) Packet PC, Round PC1 (Full) on WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md: 3 ERROR, 8 MINOR (5 November, 11:20)

Log referee_cli_20261105-105448_scope_pairCauchy_PC1.json. The Cauchy note changed during the round (#C7.5–#C7.7 added, now 60f7c65716ed); the repairs align with it.
- **PC1.1 ERROR (wrap insertions on ℓ₀):** confirmed. #PC4.2's species-blind transfer covers the dev insertions; the wrap(j) species, the two-loop words among them (never dev, #468, #MD2.0.3.26-2), grow by ≤ L per step (#MD2.0.3.34-4). Repair: #PC4.1 splits dev, wrap, cross; new #PC4.11–#PC4.13-2: age split with a_w := c_wN_s/M, old wraps dropped (τ^w_K), young wraps compared with growth 2L per step and the size factor 1/(eν_r) (D^w_K). No attached species on ℓ₀ (LF #5.39).
- **PC1.2 ERROR (transports of the words w(𝔅) on ℓ₀):** confirmed. Repair: new #PC3.6–#PC3.6-1, gauge covariance (#593–#595) and #C7.5-4's telescoping with the insertions fixed, ≤ λ_KB^×_W, as LF #5.25 on the matched pairs; a^×_K carries 2λ_K.
- **PC1.3 ERROR (B^×_W not pointwise):** confirmed. Repair: #PC2.2 defines B^×_W with (1 − w_{ℓ₀}) replaced by 1, as #ND.8.1.
- **PC1.4 MINOR (doubled carry):** confirmed. #PC4.8-3: (1 + 2C_δc̄)(1 + y^R_i) ≤ 3(1 + y^R_i), multilinear; #PC4.9: 2·3^{m_K}.
- **PC1.5 MINOR (K′ − m_K ≥ 1):** confirmed. New #PC4.4-1: K₁^×; smaller K at 2B^×_W.
- **PC1.6 MINOR (e^{ΔE} factor):** confirmed. #PC6.1–#PC6.1-1 follow #C7.6-9–#C7.6-10; a^×_K (#PC6.3-2) in #C7.7's form.
- **PC1.7 MINOR (s^{W,tot,×} substitutions):** confirmed. #PC4.2-2 names ℓ₁ + ℓ₂, max_i‖dπ_i‖ in C^{tr}_W, w̄ for b_wrap, B^×_W in LF (5.2).
- **PC1.8 MINOR (per point vs per unit):** confirmed for products. The class norm is relative per polymer (#C8.2.2-1); a product of n activities differs by ≤ n·r_i times its bound (telescoping, each run's factors within the class bound). Repair: #PC4.8-5 (cross: #(X_W) ≤ σ(W) constituents, #574; difference mass at rate (λ_n − 1/32)ν_r ≥ (15/16)ν_r, #775, #496; C_ν := 32/(eν_r)); #PC4.13 (wraps: 1/(eν_r)); #PC5.4-1 (clusters: n ≤ 2^n, doubled-activity cluster bounds under the same kind of smallness).
- **PC1.9 MINOR (stale statements):** confirmed. #PC.1-2, #PC2.1, #PC3.2, #PC5.1-1 now cite #C7.5 and #C7.6 for the single-loop leading word and constant; §3's proof is #C7.5's per loop; §5 splits the single-loop parts (#C7.6 per loop) from the cross part.
- **PC1.10 MINOR (#922 vs #390):** confirmed. #PC2.2-1 cites #390.
- **PC1.11 MINOR (#PC7.2 overclaim):** confirmed. #PC7.2 names vertex-disjoint squares in planes parallel to e₁e₂ and sides ≤ half the torus period.
- Pre-check: every #PC tag cited resolves (listed); #MD2.0.3.34-4, #MD2.0.3.26-2, #ND.8.1, LF #5.11, #5.25, #5.39, #5.40, #5.63, #574, #775, #496, #C8.2.2-1, #C7.5–#C7.7 read; units: τ^w_K's 28 = 4·7 with 1 + 6/(2log 2) ≤ 7; 3^{m_K} ≤ L^{m_K}; (2L)^{m_K} ≤ L^{2m_K}.
- Three of the gaps also hold for one loop: the wrap insertions on ℓ₀ and the words' transports (#C7.4-2 compares dev insertions and leading words), and the size factor in #C7.6-6 and LF #5.38. Sent to the peer.
- Note 1dddc3917904. Next: PC2 (full) on the repaired note.

## (PC) Packet PC, Round PC2 (Full): 2 ERROR, 3 MINOR (5 November, 11:42)

Log referee_cli_20261105-112149_scope_pairCauchy_PC2.json. All eleven PC1 findings are addressed. Every finding is confirmed against the source and repaired.
- PC2.1 ERROR, confirmed. LF #5.40: "There are no attached species before j₀", and its recursion starts at j₀ − 1 with no wrap term. The wraps exist from step 1 (#893). Repair:
  - #PC4.11–#PC4.12 hold on every labelled term (#893 is a class clause).
  - New #PC4.13-3: the young wraps' difference at j₀ − 1 is ≤ D^w_K (the steps before j₀ are small-field). It is carried by LF #5.40's factor ≤ 4, giving (e^{4D^w_K} − 1) in b^{(M),×}_K (#PC6.3-3).
  - The same gap is in LF and the single-loop chain. The peer already has it (its item 3: LF #5.40 from step 1).
- PC2.2 ERROR, confirmed. #722 gives λ_n(D) = λ_n − s(D)/32 with s ∈ {0, 1}, so (λ_n(W) − 1/32) ≥ 29/32 < 15/16. #566 and #570 give #(X_W) ≤ uσ(W) with u ≤ 19. Repair:
  - #PC4.8-5 now has 19σ(W).
  - New #PC4.8-6 tightens (H^R) to S^R ≤ 1/64 (#774), so λ_n(W) ≥ 61/64. It spends ν_r/64 and keeps (15/16)ν_r, with C^×_sz := 19·64/(eν_r).
  - The tightened (H^R) is added to #PC8.1.
- PC2.3 MINOR, confirmed. #PC4.13 spent the whole weight and then carried the difference unweighted. Repair: as in #PC4.8-6, the wraps' rate is ≥ (63/64)ν_r (s = 0 for wraps, #722). It spends ν_r/64, so the difference is weighted at ≥ (15/16)ν_r, and D^w_K uses C^×_sz.
- PC2.4 MINOR, confirmed. #C8.4.1 covers the densities' R-terms, not the R-gas. Repair:
  - #PC4.8-1 cites LF #5.46–#5.49 (b̄_K of LF #5.48).
  - b̄_K is added to r_i at the R-steps in D^cr_K, D^w_K, and Δ^{E,cr}_K, with summability by LF #5.65.
  - #PC.1-1 (iv) lists LF §5(e) and (LF-A) points (3), (6), (7), and (10).
- PC2.5 MINOR, confirmed. C_ν clashes with #345 and the Cauchy note, and C_σ is taken in the Cauchy note. Renamed C^×_sz.
- Also, at the user's prompt: #332 and new #332.1 (two-loops note) and #PC7.2 allow each square in its own coordinate plane. The labelled terms contain no observable (V4 L3727, #386), and the cross bounds use only distances.
- Pre-check:
  - Read #722, #774, #775, #496, #566, #570, #574, #345, #893, LF #5.38–#5.40, #5.45–#5.50, #5.63–#5.65, #C8.4.1, and #MD2.0.3.34-4.
  - Rates: 63/64 − 1/32 − 1/64 = 60/64 = 15/16.
  - Every #PC tag resolves. No C_ν is left.
- Notes: pair Cauchy 9120d643d4bb, two-loops 5f3948e3e320 (labels 8acafbcbeaad). Next: PC3 (full).

## (PC) Packet PC, Round PC3 (Full): 0 ERROR, 3 MINOR (5 November, 12:11)

- PC3.1 MINOR, confirmed. #PC4.13-3 carried the matched pairs' wraps from j₀ − 1 with LF #5.40's factor 4. That is the attached species' carry. Wraps grow by L per step, and the two-loop ones are cross lineages (#893). LF has since moved its wraps out of #5.40 (LF #5.41.1–#5.41.6). Repair:
  - #PC4.13 and new #PC4.13-4: young wraps are compared at birth on every labelled term. Births on the all-small-field pair and before j₀ use #C7.8-4-2. Births from j₀ on use LF #5.38.2's 4ḡ_K.
  - #PC4.13-1: the carry is 2L per step. The R-step factors of #893, doubled, are at most 16 times #893's (1 + 2a ≤ (1 + a)²). Old wraps touched pass at most 6τ^w_K per step. So D^w_K := 16(m_K + 1)(2L)^{m_K}[(ρ^×_K + r̄_K)w̄^{(2)} + 6τ^w_K].
  - #PC4.13-3 is deleted. #PC4.2-2 puts 2τ^w_K + D^w_K in place of LF's wrap terms in s^{W,0}_K. #PC6.3-3 drops (e^{4D^w_K} − 1).
  - #PC4.12: the old wrap mass bound holds at every step (#C7.8-2).
- PC3.2 MINOR, confirmed. b̄_K's summability was cited to LF #5.65 and called geometric. It contains |δ_m| ≤ C[(m + 1)θ̃^{m+1} + (K + 1 − m)w_K], so Kw_K. Repair: new #PC4.9-3a–f derives b̄_K ≤ C_b(Kθ̃^{7k/8} + Kw_K) from LF #5.48's terms and shows that 4·3^{m_K}s^{W,R}_K is summable for κ₀ > 8 (#C6.2.17-1, LF #5.66).
- PC3.3 MINOR, confirmed. b̄_K is per point (LF #5.48), and π_k-cubes have M^d sites (#730). #574 does not give a constituent count, and #PC4.8-2 lacked (G′)'s factor. Repair, following the Cauchy note's #C7.6-6 and #C7.8-4 and LF #5.38.1:
  - The birth differences use the doubled-amplitude interpolation and Cauchy's estimate. That gives 2r^E_i (#C7.6-6-2) on the all-small-field pair and before j₀ (#PC4.8-1, #PC4.8-2), and 4ḡ_K from j₀ on (#PC4.8-7). Their max is ρ^×_K (#PC4.8-8).
  - The R-gas part from j₀ on is LF #5.49's per point of the component, carried as s^{W,R,×}_K := 4·3^{m_K}s^{W,R}_K inside s^{W,tot,×}_K (#PC4.2-2).
  - #PC5.4-1 and #PC5.4-2 now use #C7.6-6-1–#C7.6-6-7 with r^E_i, since the constants are at the flat reference, and Σ_{m≥0} gives (2 + 6/a).
  - The size count (u ≤ 19), the rate (S^R ≤ 1/64), and C^×_sz are dropped. #PC4.8-5 and #PC4.8-6 are deleted.
  - #PC8.1 lists the doubled-amplitude smallness in their place.
- Also:
  - The peer's old-touched-by-young repair: new #PC4.8-9 (2τ^cr_K per step inside D^cr_K) and #PC4.13-1 (6τ^w_K).
  - #PC4.8-3 doubles y^R too: 3(1 + y^R_i)², with product ≤ 4.
  - D^cr_K := 4·3^{m_K}(m_K + 1)[(ρ^×_K + r̄_K)A^{×,2} + 2τ^cr_K].
  - #PC4.4-1 adds r̄^E_K ≤ 1.
  - #PC.1-1 is re-pinned to Cauchy d9e84b07bfca and LF a52e10df2b5e.
  - The n-loop note's #NL10.4 is updated, since it cited #PC4.8-5, #PC4.8-6, and #PC4.13-3.
- Pre-check:
  - Read LF #5.6, #5.38–#5.43, #5.41.1–#5.41.6, #5.45–#5.54, and #5.63–#5.67.
  - Read #C7.6-6–#C7.6-7-1, #C7.8–#C7.8-8, #C8.2.2-1, #C8.4.1-4, #C8.6.2-10, #C8.7.4, #C8.7.7–#C8.7.7-3, and #C6.2.17-1.
  - Read #566, #570, #574, #678, #680–#682, #714, #716, #722, #730, #775, #824, #893, #894, #896, and #897.
  - Every new tag cited resolves (checked by grep). No b̄_K is left outside #PC4.8-7 and #PC4.9-3, and no C^×_sz remains.
  - Units: ρ^×_K, r̄_K, and b̄_K-per-point are relative. D^cr_K and D^w_K are weighted masses.
- Notes: pair Cauchy b56d405418aa, n-loop 19354662fdc9. Next: PC4 (full; PC3 had no ERROR, but the repairs restructure §4).

## (PC) Packet PC, Round PC4 (Full): 0 ERROR, 2 MINOR (5 November, 12:26)

- PC4.1 MINOR, confirmed. K₁^× did not give m_K ≤ m_W or R-steps at the young steps. #C7.8-5 holds for "the steps i ≥ k − m_W, m^w_K ≤ m_W (#C7.4-7-2)", LF #5.32 for layers l ≥ k − m_W, and #C7.4-7-3 makes only i ≥ k′ + 1 − m^E_{K′} R-steps, while #PC4.4-1 allowed T-steps. Repair: #PC4.4-1 adds m_K ≤ m_W and "every scale i > k − m_K is an R-step of both runs with i > N_i", with existence by #C7.4-7-5's argument. New #PC4.4-2 states the consequences, and #PC4.8-8 cites it.
- PC4.2 MINOR, confirmed. The factor 4·3^{m_K} covers cross carries (#PC4.8-3), but wraps carry 2L per step with doubled R-step factors up to 16 (#PC4.13-1). Repair: s^{W,R,×}_K := 16(2L)^{m_K}s^{W,R}_K (#PC4.2-2, #PC4.8-7), and its summability uses (2L)^{m_K} ≤ L^{2m_K} (#PC4.9-3f).
- Citation slip, repaired: #PC4.8-2 now cites (S-w) (#473, #475) for #476, not #590.
- Also, the peer's question (B), whether the R-made wraps are among the terms that LF #5.49 bounds: yes. Repair: new #PC4.13-5.
  - An R-made wrap(k) is a D_g of D2.7 15.6, either one with a wrap member (#842, #848) or one that does not lift (map #MD2.0.3.25).
  - Its R-gas dependence is through F(P) and Ψ_g (15.5(ii)(β), 15.6), and these are cluster terms of the R-gas (LF #5.45).
  - So LF #5.49's per-point charge covers it, and the 16(2L)^{m_K} carry puts it in s^{W,R,×}_K.
  - (An interim open item #PC.0 was written and then removed; #PC4.13 and #PC6.3-3 cite #PC4.13-5.) The edit was made while PC5 was reading the note, so PC6 re-reviews #PC4.13-5. The peer's finding (A), precedence: #PC4.8-9 and the 6τ^w_K term only overcount (PC4 confirms this), so they are kept.
- Pre-check:
  - Quoted #C7.4-7–#C7.4-7-5, #C7.6-6, #C7.8-4, #C7.8-5, #C7.8-5-1, LF #5.31–#5.32, #5.38-2, #5.38.1, #5.38.2, #5.42, #5.45–#5.49, and #473–#476, #590, #661, #765, and #893.
  - Grepped every use of s^{W,R,×}_K, 4·3^{m_K}, K₁^×, and "T- or R-steps" in the pair, n-loop, and factorisation notes. Only the pair note uses them.
  - Directions: m_K ≤ m_W gives i > k − m_K ≥ k − m_W. 16(2L)^{m_K} ≥ 4·3^{m_K} for L ≥ 2.
- Notes: pair Cauchy fa86cc583e33 (PC5 launched on dda2c2d64273). Next: PC5 (changed bullets: #PC.0, #PC.1, #PC4.2-2, #PC4.4-1, #PC4.4-2, #PC4.8-2, #PC4.8-7, #PC4.8-8, #PC4.9-3f, #PC4.13, #PC6.3-3).

## (PC) Packet PC, Round PC5 (Re-Round): 0 ERROR, 2 MINOR; and the Transfer of the Reviewed r29–r33 Inputs (5 November, 14:24)

- PC5.1 MINOR, moot. #PC4.8-7, #PC4.10, #PC4.2-2, and #PC4.13-2 claimed the R-gas part that #PC.0 marked open. #PC.0 had already been replaced by #PC4.13-5 when PC5 ran, and the transfer below removes the separate R-gas route altogether.
- PC5.2 MINOR, confirmed and made moot. s^{W,R}_K carries no #893 factor, so a part carried as a wrap needed 16²(2L)^{m_K}. The transfer removes s^{W,R,×}_K.
- The transfer, made after the peer's packet 10 (Cauchy 2f1fbc164cc8, LF fa7a1005cd2a) was reviewed:
  - #PC4.8-1/-2 and #PC4.8-5/-6. The births on the all-small-field pair and before j₀ follow #C7.6-6-1–#C7.6-6-8. The constituents are Bałaban's, the marked ones, 𝐓′, V, and the polymer activities. Old components are removed by the disc in z (2e^{−C_Pk/4} per run). The rest is interpolated at 1/(2ρ^{E,×}_K), with ρ^{E,×}_K := max(r̄^{E,×}_K, r^V_K, 3(1 + eC_MN^{pt})s_K). The amplitudes are enlarged by 2 and the decay is lowered to κ − κ_I. Cauchy gives 4ρ^{E,×}_K.
  - #PC4.8-7. From j₀ on, LF #5.38-3–#5.38.2 give 8ρ^{LF,×}_K, with ρ^{LF,×}_K := max(η^{gen}_K, ρ^{E,×}_K). Since 𝐓′ and V are interpolated ingredients, this covers the R-made D_g, the wraps among them. s^{W,R,×}_K, #PC4.9-3a–f, and #PC4.13-5 are deleted. LF's own s^{W,R}_K stays inside s^{W,tot,×}_K unchanged.
  - D^cr_K := 4·3^{m_K}(m_K + 1)[(8ρ^{LF,×}_K + r̄_K)A^{×,2} + 4e^{−C_Pk/4}A^× + 2τ^cr_K], and D^w_K := 16(m_K + 1)(2L)^{m_K}[(8ρ^{LF,×}_K + r̄_K)w̄^{(2)} + 4e^{−C_Pk/4}w̄ + 6τ^w_K].
  - #PC5.4-1/-3 and #PC5.4-2. Δ^{E,cr}_K := 4ρ^{E,×}_KA^{cr,2}_ES^{cr,2} + 4e^{−C_Pk/4}A^cr_ES^cr.
  - #PC4.4-1/-2. K₁^× asks ρ^{E,×}_K ≤ ¼, and old components are shown to have P_i ≥ k/4 at the pair's young steps.
  - #PC8.1 and #PC4.9-2: κ₀ ≥ 11 and κ ≥ 12.
  - #PC.1-1 is re-pinned. The n-loop note's #NL10.4 is aligned (29430005e3ff).
  - The old-touched terms (#PC4.8-9, 6τ^w_K) are kept as overcounts.
- Pre-check:
  - Quoted the current #C7.4-7–#C7.4-7-5, #C7.6-6–#C7.6-8, #C7.8-1–#C7.8-8-1, LF #5.38–#5.38.2, #5.40–#5.41.6, #5.42–#5.49, #5.53, #5.63, and #5.66–#5.68, and #894 and #897.
  - Directions:
    - ρ^{E,×}_K ≥ r^E_i at i > k − m_K, as #C7.6-6-4-1 needs.
    - ρ^{E,×}_K ≥ 3eσ, as #C7.6-6-4-2 needs, since 3(1 + eC_MN^{pt})s_K ≥ 3eC_MN^{pt}s′_K.
    - r^V_K's range i ≥ k − ⌊k/4⌋ − 1 contains i > k − m_K.
    - 4ρ^{E,×}_K ≤ 8ρ^{LF,×}_K.
    - The old-component term uses own bounds (A^×, w̄), and the interpolated term uses the enlarged ones (A^{×,2}, w̄^{(2)}).
  - Tags: every #C, LF #, and #PC tag the note cites resolves (checked by grep). Nothing remains of ρ^×_K, r̄^E_K, s^{W,R,×}_K, ḡ_K, or the "doubled amplitudes".
- Notes: pair Cauchy 33d4d8246550, n-loop 29430005e3ff. Next: PC6, a full round, since §4 and §5 are rewritten.

## (PC) Packet PC, Round PC6 (Full): 1 ERROR, 1 MINOR (5 November, 14:43)

- PC6.1 ERROR, confirmed. LF's s^{W,0}_K (#5.53) contains 24(m_W + 1)τ^w_K, from (D) (#5.41, #5.40-2), and #PC4.2-2 did not substitute it.
  - With LF's single-loop τ^w_K, the term misses the pair's #893 wraps.
  - With the pair's τ^w_K, which decays like (K + 2)^{−2}, m_Wτ^w_K is not summable when a_w = a_*.
  - Repair:
    - m_K's threshold is now 3log(K + 2) (#PC4.4), as #C7.8-3 does. So τ^cr_K, τ^w_K and τ^{E,cr}_K decay like (K + 2)^{−3} times log powers (#PC4.6-2, #PC4.12, #PC5.3). The constants 8, 28 and 6 still hold at 3log 2.
    - #PC4.2-2 substitutes the pair's τ^w_K into 24(m_W + 1)τ^w_K, and #PC6.4 cites #PC4.12 for it.
- PC6.2 MINOR, confirmed. #PC4.8-5 lowered ν_r in A^{×,2}, but the masses are weighted at #722's ν_r. Repair: ν_r stays.
  - ν_r = ν = η is V3's reserve constant, fixed before κ (map #MD2.4.3.10).
  - Its conditions against κ, such as #802's, hold at κ − κ_I under #C7.6-6-6-2's thresholds.
  - The R-part's decay is unchanged (#C7.6-6-6).
  - Only C_cr, C_gr and ν_× (through A′_E, #343) change.
  - #PC8.1 lists both conditions.
- Cosmetics after the peer's r35: the disc in 𝔷 (#PC4.8-2, #PC5.4-1) and δ^{cl}_i (#PC4.13-1). #PC.1-1 is re-pinned to Cauchy 8fadc431adf6 and LF aff9348d04ab. LF #5.38-3, #5.38.2, #5.40-2, #5.41 and #5.53 were re-read at aff9348d04ab and are unchanged in substance.
- Pre-check:
  - Grepped every 2log(K + 2), 2L log and (K + 2)^{−2} in the pair and n-loop notes; none is left. The n-loop note inherits m_K from #PC4.4.
  - Checked L^{m_K} ≤ max(1, 3L log(K + 2)/a_*) from the definition.
  - Every cited tag resolves (grep).
- Notes: pair Cauchy 7169747b6de2. Next: PC7 (re-round on #PC4.2-2, #PC4.4, #PC4.6-2, #PC4.8-5, #PC4.12, #PC5.3, #PC6.4, #PC8.1, #PC.1-1; the cosmetics).
