# D2 map: triage of round 33

Review read in full: it1-d2-4s12mc-20261025-r1. It covers the m-c repair in D2.2(6)(c)–(d) and D2.4(12)(c)–(d).

Verdict: the m-c repair is correct and sufficient, subject to one minor wording repair (m-2). There are no fatal or serious items. The reviewer checked:
- the *Localisation* expansion: exact, absolutely convergent and local;
- the vacuum-link rule: with the second and third rules, it makes the domains of distinct groups compatible;
- the new joined pairs: all are (ii) pairs, so the covering lemma holds;
- the expanded vacuum-factor constants (2^s, nue^{nu}, e^{5c}, e^{6c}, and the weight 2|φ^T|_sup·2^s): all check.

User decision recorded: κ ≥ κ_D′ is accepted. The map's labels at D2.4(2) *The condition on κ*, (12)(d) and (12)(g) now say so. L₀ = 5000 and β₀ ≤ 1/2 were accepted earlier (R32 triage).

User decision recorded: the linked-hull arc rule of D2.2(6)(d) is accepted. The (d) heading now says so.

User decision recorded: (R-m′), q := min(q₀, q₁) > p₀, is accepted **provisionally**, together with SW closure §2's q₀ = q₁ > p₀. The user's words: "I accept it for now, though be cautious about it during future review if such an extra requirement appears". The labels now say this at:
- the map: (12)(f), (13)(d), the R-m entailment note (D2.2), l.170, the (Z) status (l.1136) and D2.4(5) (l.1423);
- SW closure §2.

Future reviews must flag any printed condition that bounds q₀ or q₁ above in terms of p₀.

User decision recorded: (T2) is accepted. This is the split e^{−(κ_s−3)#(G_M)} = e^{−ν_e#(G_M)}e^{−(κ_s−ν_e−3)#(G_M)} before (11)(d), under κ_s − ν_e ≥ κ_s^{(12)}. The map at (12)(f) quoted the factor as e^{−κ_s#(G_M)}; it is now aligned to (11)(d)'s actual factor e^{−(κ_s−3)#(G_M)}, the closure's form. The labels now say "accepted" at:
- the map: (12)(f) and (13)(d);
- the closure: §5.2 and the §8 list.

User decision recorded: (T0), the lineage-form re-run of (12)(e)–(f) and its product form in D(k)(ii′-a), is accepted. The labels now say "accepted" at:
- the map: l.302, l.308 and (12)(f);
- the closure: §5.2 (T0), the §5.3 derived line and the §5.5 derived line.

§5.0's carried-weight amendment (e^{ν_rσ}e^{(3/8)ν_e·ext^{coll}} inside (ii′-a), each insertion counted once) remains for review.

All edits were made in WILSON_IT1_D2_STEP_MAP_2026_10_22.md with Edit. The map still has 1614 lines. The closure is unchanged (177 lines). V4 b35c60e537b8 is unchanged.

## Items

- **m-1.** The cluster set is infinite, so the expansion is exact by absolute convergence: Σ_{𝒞≁M}|e^{±y_𝒞} − 1| ≤ Σu_𝒞 ≤ 3c#(M), by D2.4(2)(g) in sup form. Added: "The expansion is done before grouping". For fixed 𝒮 and 𝒦, the groups of (d), Ĥ(G) and Y_𝒢 are defined term by term.
- **m-2.** The joined pair no longer says "of another group". A vacuum link at M is incompatible with M′ ≠ M or with a vacuum link at M′ ≠ M. The pair is (I(M), I(M′)), which is fixed data independent of the merge order.
- **m-3.** The double use of the flat factor is removed:
  - (6)(c) now defines Q° := exp(Σ_Tε_TΨ°_≥(T)) = exp(Σ_𝒞(s − 1)_+φ^T(𝒞; 1, 0, 0)) as the whole flat factor. This is D2.3(3)'s vacuum part, which is expanded in occurrences and not split over the groups.
  - Ĥ(G) := ∏_{T⊆G}(e^{ε_TδΨ_≥(T)} − 1)·⊗Ĥ(M).
  - e^{−Ψ°(M)} stays in Ĥ(M), with |e^{−Ψ°(M)}| ≤ e^{c#(M)}. It enters c_𝒢 = Y_𝒢(1, 0) of D2.3(2), from whose gas D2.3 extracts δm_{k+1} and z_{k+1}.
  - Q°(𝔊) is renamed Q° in *Properties* and in the θ bound. The bound |Q°| ≤ ∏e^{θ(G)} still holds by the multiplicity bound.
  - The (12)(f) cube cost stays at 24c, since no per-group flat factor is kept.
- **Q1 evidence (𝐉 locality).** *Localisation* now cites l.622: 𝐉 is an independent variable of Cov(k). It also cites RG2 p.5 and D2.3(4)(Z-c): H(Z) depends on 𝐉 only on its dependence set.
- **n-1.** (12)(c)'s M-vertex activity is |e^{−Ψ°(M)}H̃(M)|·∏ (weights of the links). e^{−δΨ(M)} enters only through its links.
- **n-2.** "they vanish at (1, 0, 0) and are not constant".
- **n-3.** A cluster chosen by several factors is one link domain, carried at each M_T of a choosing factor. These are (12)(c)'s pairs (T, 𝒞).
- **n-4.** The members of old occurrences are "treated as old insertions of their group for the second rule". (12)(c)'s 𝒱(M) also holds vacuum occurrences; the reviewer notes this is harmless, so no change.
- **n-5.** In the *Class form*, the domain of 𝒢 together with the bonds of I(𝒢) (the U_{k+1}-transports) is the set on which Y_𝒢 depends.
- **(12)(f) arithmetic (context).** The reviewer's corrected values are 143·17/16000 ≈ 0.152 and 221/8000 ≈ 0.028. Both bounds still hold (< 8; 29.6 < 36). The map states no decimals there, so no change.

## (12)(a)–(b): accepted; the two readings checked

User decision recorded: (12)(a) (σ_{k+1} := #_{k+1} + n_{k+1}/M), (12)(b) (the reserve and extent weights in (ii-w), w_t at η_w = (5/16)η_V) and C_box ≥ 4A_E are accepted. The user's words: "I accept it, but check the readings! Stop calling something a reading if you could check what it means".

The two items labelled as readings inside (12)(b) were checked against V3 and are no longer readings:
- **M_Λ pins on the complex domain.** V3 L2674 and L2722 define M_Λ(W) = (1/k(W)!)∏_Zρ_tm(Z)∏_j|Φ|^+_Λ(𝔠_j). Here m(Z) = ε_*e^{−λ_*ℓ₁(Z)} (L2647), and |Φ|^+_Λ is the incompatibility-tree sum of the m(D_i). V3 calls it "defined without reference to the source data". So the pins of L2791 involve no background and hold at real and complex backgrounds alike. The complex part is the domination of the group quantities by M_Λ(W) at 𝐔. IT-1 §3e(3.9), l.1075, derives it: (c5-5-8) holds at 𝐔 with the extra factor e^{C_UL_fρ₁} ≤ e^{C′𝔰ρ₁}. The map already paid this factor as the complex 1/8.
- **Hull form of (E₁).** V3 Lemma c4-6-env (L4611 (a)–(b), proof L4615) defines 𝔈(W) = 𝔑_{R_e}(X(W) ∪ π₁(ℋ(W))). The lemma proves that 𝔈(W) is connected under maximum-norm adjacency and that |𝔈(W)| ≤ A_E𝔰(W). So any two of its cubes are at index distance ≤ A_E𝔰(W) − 1, and it contains X(W) and the cube of every traversal of the hull. This is printed and checked.

Also:
- A_E = 9(2R_e+1)⁴ ≥ 729, since R_e ≥ 1, so SW closure's C_box ≥ 6 follows from C_box ≥ 4A_E.
- The map's pointer "(l.1040)" for e^{C′𝔰ρ₁} ≤ e^{η𝔰/8} is now written "IT-1 l.1040".

Labels updated:
- in the map: l.170 (twice), l.292, l.1391, the (12) heading, (a), (b), l.1589 and l.1614;
- in the closure: l.73 (three places), l.118 and l.159. The l.159 list now also marks (T0) as accepted, and q₀ = q₁ and (R-m′) as accepted provisionally; these were accepted earlier but were not yet marked there.

The map still has 1614 lines and the closure 177 lines. V4 b35c60e537b8 is unchanged.

## The older readings checked (23:31, 25 Oct, date)

At the user's request ("Check the older reading"), the readings of rows 1–34 of READINGS_RECHECK_2026_10_23.md were checked against the sources. Verdicts:
- **R-𝐇, R-𝐇₀: bound derived, analyticity Bałaban's.** The argument bound at complex 𝐔 comes from REG Lemma 1 (pp.79–80) iterated as in REG (1.65), with CRE (2.34)–(2.35), CMP98 Prop. 3 (p.36), (127) and (57) at complex data. Analyticity: VAR Prop. 9 on PBG's complex class (p.396), of which Ũ^c is CRE p.261's precise form.
- **Correction:** S_H = C_H(α_{0,j+1} + α_{1,j+1})e^{−R_j}, not C_Hα_{0,j+1}e^{−R_j}, because the complex averages deviate by O(α₁). Updated in the map (l.222, l.971, l.979, l.980, l.190, l.192) and in closure §2.2 (c). The conditions still hold for g_K small.
- **R-cpl₀:** printed in RG1's setting, and for simple G also derived from ONE_LOOP_PROOFS Lemma 2.1 with Cor. 8.2. **R-cpl:** Bałaban's; proved for simple G (Cor. 8.2).
- **"Lemmas 5, 6 [I]", R-I7:** identified by content (CRE p.276; RG2 Lemma 1 contains (1.34), Lemma 2 contains (1.41), and there is no other lemma in RG2 Sect. 1).
- **R-m's constant comparison:** derived given (R-m′), which is accepted provisionally.
- **R-adm, R-REG81:** printed.
- **R-dec, R-vac(i), R-x:** Bałaban's, accepted.
- **R-F₁, R-g_k:** derived.

The labels are now synced in:
- the map's status block (l.181–190);
- the entries l.192–225;
- the bodies: l.581, l.690–708, l.740–741, l.778, l.786–810, l.981–984, l.1353–1357, l.1410, l.1418;
- the closure: l.16, l.31, l.55, l.73, l.79, l.158.

What remains a reading among rows 1–34 is only **R-c Pass 5 (e)**. The step not derived is the Mayer expansion of the shifted cutoffs on the collar 𝒦₁, where |m_t| ≤ Kr with K = O(1). What closes it: K ≤ 1/2 for the conditional-mean shift within ρ₁ of Λᶜ, or a collar treatment that needs no penalty.

Readings labelled outside rows 1–34 were not checked in this pass. They are listed in the re-check summary:
- in the map: R-str, l.78, l.90, l.156, R-rep, l.1251, l.1304;
- R-17;
- in the closure: R-Z, R-𝐁, R-vac(ii) on the collar, R-dec⁺, R-src, R-ζ(a), R-ζ(b) and the §c4-10-1 radii.

The map still has 1614 lines and the closure 177 lines. V4 is unchanged.

## R-tr's tie rule (after the user's "What is R-tr?" and "Do this")

Checked whether any step of the map needs rotation or reflection covariance. None does:
- D2.3(4) uses translations by multiples of Π_{k+1}.
- D2.3(5)–(6) keep κ_v per orientation and ζ_{v,w} per corner pair, and average them over the square's own orientations; they never equate orientations.
- The two-loop placement and the lifted partitions are translations.
- The other symmetries in the map are field signs (A → −A, λ → −λ).

A fixed least-offset rule would therefore suffice for D2. The user then asked whether there is any reason not to average, saying "It would be good to be as close to Euclidean covariance as possible". No reason was found:
- The average is exact.
- Its terms are single-partition terms with weight 1/m, so the bounds are unchanged.
- It lifts to larger tori.

So the equal-weight average is kept, and the decision is settled. The other free choices are also taken hypercubic symmetric (ζ̃_□ and the grid walk families).

Full hypercubic covariance, checked after the user's "Check it" (23:58, 25 Oct, date): on ℓ₀ the step is covariant under the hypercubic group about the centre p of a coarsest-partition cube and under period translations (RTR_PROOF_PASS, *Hypercubic covariance*).
- Partitions: grids through 0 with sides powers of the odd L (RG1 p.251, p.257, RG2 p.3), so p is a site of every T^{(k)} and a cube centre of every grid; equal torus sides (RG1 p.251).
- Contours and gauges: RG1 p.252–254 replaces CMP98's axis-ordered average by the average over all orderings ((0.4), (0.11), (0.12)), and gauge-fixes through 𝐔(y,x) ((0.14), CRE (1.5), p.247–248). The single axis-ordered contours left (CMP98 p.24, RG1 (3.26), REG (1.19), VAR (124)) are proof devices or orbit representatives and define no object.
- Printed: RG1 p.263, Thm 3, p.269; CRE (2.29), (3.39). Profiles: CRE (3.40)'s h even as printed; RG1 p.270's ζ and PRT1's h taken even (they exist; our convention).
- Our objects are covariant jointly with C (V4's cyclic base is relative to C's traversal list).
- Map edits: l.186 (convention: even profiles; consequence stated), l.1087 (C's corner at p, not at a grid corner: sites are cube centres, so "a corner at the common origin of the partitions" was not a site).
- Consequence: κ_v and ζ_{v,w} take one value each, so δm_{k+1} is the same for every plane and orientation. After the user's "Do this" it is stated in the map: D2.3(5) *Independence* (signed permutations about the origin act transitively on orientations and on ordered orthogonal pairs; (H3)'s tori are cubic, V4 L155), l.118 (μ = κ_v/Π₂ for every v), l.1010 (step 1), l.186. No bound uses it.
- Side finding: RG1 p.270's "derivatives up to the second order bounded by 5" for ζ cannot hold (|ζ″| ≥ 36 is forced); constants only.

Updated in:
- the map: l.186, l.192, l.1020, l.1103, l.1216;
- RTR_PROOF_PASS (*Choice 3 revised*);
- the READINGS_RECHECK summary.

## R-c's collar step closed (00:18, 26 Oct, date)

The user asked why R-c was still a reading, then said "Yes" to the proposed repair.
- Why the old route could not work: the cutoff threshold r on the collar equals the outer field's bound r, so where |m_t| is close to r the shifted test fails with probability of order one. No bound on K closes this.
- Repair (amendment A-col, RC_PROOF_PASS Pass 6): V4's collar threshold becomes ϑ_+ := min{1/(4c_hC_H^near), 1/(2c_hK_h)} (V4 uses ϑ only through upper bounds; V3 and V4 searched), and the collar tests run on the whole outer layer 𝒪(Λ) within ρ_L of Λ, with V4's rounds, 𝒬⁺ retreats and Fill. Then |m_t| ≤ r/2 on every bond of Λ, and Pass 5 (e)'s penalty holds everywhere.
- New bad bonds: pointwise factor by R-d″'s (D1) with the local gap (D-b⁺) (cube condition near Λ₁ ⊂ Ω₁^{∼−2}); history side by V4 Lemmas c5-2-3, c5-2-4 with dist(e, Λ₁) ≤ ρ_L, so p_e ≤ q_{ϑ_+} and the coverage average keeps its form with N⁺_ret.
- Status: R-c derived, no reading left in rows 1–34; not reviewed. Map l.185, l.188; READINGS_RECHECK summary; V4 change recorded for the next manuscript version.
- Noticed, not changed: map l.360, l.696, l.705, l.929, l.1178 still say "reading R-cpl₀", while the status block (l.181–190) and re-check row 10 record R-cpl₀ as derived from Cor. 8.2 for simple G.

## Next

No re-review is launched. The verdict was correct and sufficient. The m-1, m-2, n-1 to n-5 repairs use the reviewer's wording. m-3 follows the reviewer's first option.
