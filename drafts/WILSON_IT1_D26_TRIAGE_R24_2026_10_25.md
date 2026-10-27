# Triage of review round 24 (D2.6 closure, 25 Oct 2026)

Round 24: six packets it1-d26-s{2,4,5,6,7,9}-20261025-r5, launched 04:10:53 GMT (claude-opus-5-5, xhigh), on WILSON_IT1_D26_CLOSURE_2026_10_24.md after the round-23 repairs and the O5 repair (SHA 500bef054c0e at launch). Each report read in full; dispositions below. Edits by Edit only.

## s4 (§4, kind (γ); landed 04:15:55)

No fatal, no serious.
- m-A (4.2, map D2.1(4) *Constants*): "ε₁ ≤ a₁ free", "ε_H ≤ 2C₁a₁" wrong. Checked against VAR p.305 (corrected transcription): (172) holds "for ε₁ sufficiently small", and a₁ appears only in (169)'s M′ε₁ ≤ a₁; Prop. 9 (p.309) speaks of "small configurations V′". **Repaired:** ε_H < 2C₁^{VAR}ε̄₁, ε̄₁ VAR Sect. G's threshold (including M′ε̄₁ ≤ a₁), strict inequality; closure 4.2, §8 readings line (R-dec⁺), §8 review list; map D2.1(4) *Constants*.
- m-B (4.3): an inherited wrap(j) as first species gives wrap with 2.1(e)'s bound and growth L. **Repaired** in 4.3.
- m-C (4.3): the remaining kind-(γ) groups whose set does not lift are wrap(k+1) by 2.1(e)'s precedence; rule change (3) only for those that lift. **Repaired** in 4.3.
- n-1 (4.1): layer k's width 6LMR_{k+1} ≥ RM₁ via CRE (2.9) R_k ≤ (L+1)R_{k+1} and M ≥ M₁. **Repaired** in 4.1.
- n-2: C₁^{VAR}. **Repaired** (4.2).
- Reviewer's note that 2.1's rule change (3) has the same omission as m-C: 2.1(e)'s precedence sentence already states it ("the wrap test comes before (i)–(iv)"); rule change (3) is read after it. No edit.
- Superseded later in this round: m-A's ε_H < 2C₁^{VAR}ε̄₁ misread (172); corrected to ε_H ≤ C₁^{VAR}ε̄₁/2 under s9 m-1 below.

## s2 (§2.0–2.5, §3)

- **S-A (serious, accepted): 𝐏^{(k)} at complex σ_k.** The round-23 claim that 𝐏^{(k)} depends on σ_k only through the configuration was false: RG2 (1.41) writes 𝐏^{(k)}(g_k, U_{k+1}, B), a function of the fluctuation field; CRE p.276 moves exactly the σ_k-dependent terms with Y ⊄ Λ_{k+1} to (3.43), Ũ^c_{k+1}(Y,(1+β)α̃₀,(1+β)α̃₁) × {A : supp ⊂ Y∩Λ*, |A| < C₁p₁(g_k)}, which has no A_k variable; RG2 Lemma 2 (p.11) and p.10's analyticity in B′ are [I]'s whole-lattice statements. Sources read: CRE pp.270–278, RG2 pp.9–11. **Not closable from the read sources in this pass: recorded as OPEN (O6)** in §2.2 (1′), §0 R2, §8. What closes it: a re-run of RG2 §1 with CRE's {Ω_j}-operators for B = (A_k, A), after finding why (3.43) restricts A to C₁p₁(g_k). §2.2's label: derived for the source term and the (1) potentials, OPEN for 𝐏^{(k)} and V^{(k)}.
- m-1 (reference point): the comparison is at (σ_{k,0}, 𝐔) with x_b := −tA(b)(K(𝐔)ζ)(b). **Repaired** (§2.2).
- m-2 (KP condition): restated per cube, 2C_KO(M^d)e^{a}r_kr_{ω,k} ≤ c_KP. **Repaired** (§2.2).
- m-3 (R-src should name (3.27)): R-src restated to cover (3.27) (p.271, p.276) and complex (𝐔, 𝐉). **Repaired** (§2.2, §8).
- m-4 (wording): "never complexifies the outer field A_k". **Repaired** (§2.2).
- m-5 ((2.42) covers only 𝐁^{(j)}): new item (1) for 𝐄_k, 𝐑_k, 𝐁_k and A(·), with the inductive assumptions (2.26)–(2.40) for 𝐄 and 𝐑; (1′) for 𝐏^{(k)} and V^{(k)} is O6. **Repaired** (§2.2).
- m-6 (precedence in *Merged groups*): one order, inherited → wrap → (i)/(iii) → (ii) → (iv). **Repaired** (§2.1).
- m-7 (O1 status): §0 R6, R14, §3's label and §4's label say "O1 derived (25 Oct), gluing redone for re-review". **Repaired.**
- m-8 ((ii)-form label pointer to SW §0(a)): now cites SW §1(a1). **Repaired** (§2.2).
- m-9 (R-𝐁 additions): (2)–(3) derived from (2.41): every term of 𝐁^{(j)} satisfies X ∩ Z_j^∼ ≠ ∅, and Z_j^∼ ⊆ Ω_{j+1}ᶜ ⊆ Λ_{k+1}ᶜ by (G1) and (2.9). Only (1), the re-expansion, stays a reading. **Repaired** (§2.3).
- m-10 (one rate): c := min(c^{(1)}, c_*′) with c_*′ := min(η_V/C_F, ν_e/8, κ/4) in every N_j; map l.382 amended. **Repaired.**
- m-11 (R-fr wording): "presupposed by Bałaban's cluster expansion of (3.27), (3.29) over the support", pp.271–272, 277–278, p.269 l.17–19. **Repaired** (§2.3, §8).
- m-12: "is not contained in Ω_k". **Repaired** (§2.1).
- m-13: the structural reading of (i) moved into 2.1's rule. **Repaired.**
- m-14 (stale context): map (6)(e) *Propagation* j ≥ 1 bullet marked as at the superseded radius (map l.966); *The condition* restated at r_{ω,j} = g_j^{1/2}, 16C_Hα_{0,j+1}g_j^{−3/2}e^{−R_j} ≤ 1 (map l.979); SW (a1)(ii)'s parenthetical corrected; SW (a3) gains a pointer to closure §2.0 and rule changes (1)–(4) with their order. **Repaired.**

## s5 (§5, the carry lemma)

No fatal, no serious.
- Minor 1 (base rate): c_*′ := min(η_V/C_F, ν_e/8, κ/4), one rate in every N_j (as s2 m-10); §7.1 re-checked. **Repaired.**
- Minor 2 (extent of a descendant): the members' term is now 2Σ_{D″∈𝔅(𝒢)}σ(D″)/L over every fixed member, the first member included, in (T3) and 5.5; paid by e^{2aσ/L} ≤ e^{(ν_r/16)σ} (L ≥ 6) from each member's reserve. Y_W as a set is defined in 5.0 (the π-cubes meeting X_W, map l.622, or Q_W), distinct from the value Y_W. **Repaired.**
- Minor 3 (positions of a fixed root): 81Mσ(D) by map (14)(d), plus |win(D)| ≤ 41(diam_D + 1) ≤ 82Mσ(D) (map l.1625), so 163Mσ(D); rooted-sum condition 163Mε^{new} ≤ ν_r/4 added to §8. **Repaired** ((T0)).
- Minor 4 (reserve budget): c_D := 0 for fixed members; C_b := 8/7 with an explicit budget of e^{ν_rσ}: 5/8 (w̃ and be^{b/2}) + 7/32 (polynomial; sup_x(x/4)e^{−7x/32} = (8/7)e^{−1}) + 1/16 (transports) + 1/16 (merge extent) + 1/32 (occurrence charge) = 1; each charge spent at most once per term and step by the hard core. **Repaired** (5.5).
- Minor 5 (M-free merges): "beyond the occurrence charge and the hull-gap extent, paid from the members' reserves". **Repaired** (5.5; done before this triage).
- Minor 6 (labels 5.1, 5.3): not closed at n = 1, nor for members carrying j = 0, 1 slot values at any later n, through the map's *The inclusion* (k = 1 base points on Ω₁∖Ω₂, O3); 5.1 names the ω-radius amendment. **Repaired.**
- Minor 7 (stale pointers): the closure's §2.2 pointer was already fixed (s2 m-8); SW §0 now cites §1(a1)'s scope. **Repaired.**
- Minor 8 (cosmetics): "c̄ bounded"; g_* := sup_{m≤N+1}g_m (R_{N+1} enters δ_N); 4.3 (γ2)'s split (½, ½) in 5.0; "the att(j, Z) term of A_j(Z)"; "C_Mb_n·pl ≤ b_n/ᾱ_n". **Repaired.**

## s6 (§6, the leading word)

No fatal, no serious.
- m1 (class (III) argument size): c_A := n_𝓔^{1/2}c_Gc_h2O(L²) from V3 L3742 (read); ‖A‖ ≤ 2c_Aε₀ via 4K_*H_*ϑ_* < 1. **Repaired** (6.1).
- m2: the gap ≤ 3ℓ_s − 4ρ_L < LM; 6.4(a)/(b) renamed to 𝒩₁. **Repaired** (6.2, 6.4).
- m3: C_I″ used throughout for the class-(I) slot bound. **Repaired.**
- m4: new g₀-thresholds 4c_Aε₀ + C_𝖢′g₀ ≤ θ₀, C_Eρ₁ ≤ c_ℓ, H′C‖A‖ ≤ 1 listed in §8. **Repaired.**
- m5 ("paid from Pol(X)"): §7.1 states that a label polymer X carries LFR II's factor e^{−κ₁(X)−2p₀(g₁)} (§3j(6)), and the retreat factor 4^{#ℓ-cubes(X)} is paid from the share 3·2^dlog 2·(d₁′(X)+1) carved out of κ₁(X) next to Pol(X) in 7.2's *Ledger at j = 1*, per label polymer (with s7 S-1, m7); §6.5 says the same. The §8 entry was left stale and was reworded to "carved out next to Pol" after round 25 (s6 minor 7). **Repaired** (6.5, 7.1–7.2; §8 after round 25). (Line added after round 25, s6 minor 10.)
- m6: IT-1 §3e(0) and (3.12) *What else uses m* annotated as superseded for the leading word by closure 6.4 *The step's shift convention* (frozen-m₀ form = §3j(6)'s representation, O4). **Repaired** (IT-1 note).
- m7: the 61/16 amendment noted for IT-1 D1(iii)′, (3.8) and map D(k)(iii). **Repaired** (6.5).
- m8 (φ_c/D̃ and gauge covariance): first half, at a real background D̃ is φ_c = D̃_{U₁,c} of Lemma c2-uniform-chart(ii), the unique solution with h(d_c) ≤ ρ_d (V3 L3723); at complex backgrounds its continuation by §c4-10-1's joint analyticity. Second half, *Gauge step* in R-st: from V3 L430's intertwinings and L3689's transfer statement, uniqueness in (ii) gives D̃_{U^u,c}(R_uA) = R^{(1)}_uD̃_{U,c}(A) and q_{U^u}(R_uA) = R_uq_U(A); extended to complex 𝐔 by analyticity; Φ_i = Ad^{−1}Φ_i^{st}, and every norm used is Ad-invariant. **Repaired** (6.1).
- m9: J_col note. **Repaired** (6.2).
- m10: 2R_t + 8L + 5 ≤ ℓ dropped from §8 (unused); C_linC_lw^{III}. **Repaired.**
- m11 (label naming NOT SUPPLIED V3 lines): R-st's label names V3 L3715–3747, L4881–4899, L4957–4975 and, after m8, L412–430, L3689–3712. **Repaired.**

## s7 (§7, the payment)

- **S-1 (serious, accepted): the per-X ledger at j = 1.** C_X := √d·3·2^{d−1} with Σ_{Z⊆X}(d₁′(Z)+1) ≤ C_X(d₁′(X)+1) (spanning tree); Res(Z) := (K₁/(8C_X))(d₁′(Z)+1), ε_A(1) ≤ K₁/(8C_X); Pol(X) := (K₁ − (1+C_X)B₁ − K₁/4 − 3·2^dlog 2)(d₁′(X)+1) ≥ K₁/2 under K₁ ≥ 4(1+C_X)B₁ + 12·2^dlog 2; the ledger constant renamed B₁; map l.385 amended. Transmission to step 2 stays O2. **Repaired** (7.2).
- **S-2 (serious, accepted): every step-1 species' extent.** New §5.6: every step-1 species takes its extent from 𝒩₁; ext^{𝒩,(1)} ≤ 2ext₁ + 1; n_B from (G1) and CRE (2.9) (102LM_VR₁ ≤ 6L^nM_VR_n once L^{n−1} ≥ 17(L+1)(n−1)^{β₀}); C_lin := 2(1+C_δc̄)^{n_B}; a_1 gains 205^d at j = 1; the n = 1 exposed term uses 205^d and §3i(7)'s rooted form. **Repaired.**
- m1, m2, m3: retreat-anchored masses use §3i(7)'s rooted form; budget factor 2 reserved for O2′; retreat factor carved out next to Pol(X). **Repaired** (7.1, 7.4(b)(ii)).
- m4: *Use of Res* with 2n₁ + R_{j+1} and C ≥ 8·13^d. m5: small-domain wording. m6: C̄_A^{(j+1)}. m7: per label polymer. m8: *Which M* names B₁, B_{j+1}, B_j(Z), M = M_V. m10, m11: 7.4(a) n = 1 note, C_ν. m12: the Pol note for D2.7. **Repaired.**
- m9: 7.4(a)'s label names D2.4(4) *Scope* and D2.3 for the same-activity step; §8 *Not D2.6's* lists them as given from the map. **Repaired.**
- m13: O4's closure adds per-ℓ-cube costs near Ret(Λ) and Z₁ that are not inside the share 3·2^dlog 2 or C_A(1); recorded in O4 (§8): its closure must enlarge both, with K₁'s condition. **Recorded.**
- m14 (Ret-only collar marks): checked against V3 L2713–2718 and IT-1 §3a(7)–(8): they exist. V3's bond marks decay from J₁(Λ) ⊇ I∖D(Λ), and a host mark is a fixed constant when a primitive has an input in J(Λ) ⊇ I∖D(Λ). **Repaired** in 7.1 as the fourth retreat-anchored step-1 mass. The bound is split by source: the e ∈ I∖D(Λ) summands and the constant host marks with all J(Λ)-inputs in I∖D(Λ) are booked per ℓ-cube of Ret(Λ). Per cube they are ≤ Cρ_{t,1}(r^{d_G}+1)ℓ^dc_CC_FLM, with ρ_{t,1} = C′_χg₀(1+2r)/u_*, i.e. g₀ times a polylog. They go inside the same factor-2 payment; B₁(Z) keeps the rest.

## s9 (§9, the carrier item)

- **S-1 (serious, accepted): the gluing step (2)(i).** The claim "the inside blocks of crossing bonds lie in Λ′₀" was false. **Repaired by derivation:** induction P(n): for every level-n bond c with no endpoint in Ω′_{n+1}, the glued field and U_{i+1} have the same level-n average. Inputs: RG1 Sect. 0's convention (p.251, bonds intersecting a set), VAR p.277 ("at least one end-point"), CRE (2.2); RG1 (0.4)'s one-step average depends only on the bonds in B(c₋) ∪ B(c₊); M^n = M∘M^{n−1}; Ω′_n is a union of M₁L^n-blocks with Ω′_n ⊆ Ω_n; CRE p.256's distances L^nξM₁. The global constraints c ∈ Γ_m have no endpoint in Ω_{m+1} ⊇ Ω′_{m+1}. The same induction gives the inclusion used in (B) (m-9) and M^{i+1}U_{i+1,□′} = V_{i+1} on the collar (m-5) [corrected after round 25, s9 m-A: the induction is applied to U_{i+1,□′} and Q^{s*}_{i+1}V_{i+1}, which share 𝔹_{i+1}(□′^{∼4})'s data by (2.16), with M^{i+1}(Q^{s*}_{i+1}V_{i+1}) = V_{i+1} from (0.4) and (1.3); U_{i+1} and U_{i+1,□′} share only the level-(i+1) data]. O1 is re-derived and sent for re-review. Sources read: RG1 pp.251–253; CRE pp.255–256.
- m-1 ((172)): the hypothesis is |V′ − 1| < C₁ε₁, and |B′| < 2C₁ε₁ is its consequence. New constant condition ε_H ≤ C₁^{VAR}ε̄₁/2, with ε₁ := max(data regularity, 2ε_H/C₁^{VAR}). In §9.3, ε₁ := C₁^{−1}max(2·44d²B₃ε_{i+1}, 2·30d²L²B₃(1+β₀)ε_i, C₁·data) ≤ ε̄₁. **Repaired** (4.2, §8, §9.3, map l.495).
- m-2, m-3 ((1)'s text; the inclusion via P(n)); m-4 (space (6) = (2) ∩ (3)); m-6 (δ-function and (G3)); m-7 (∇𝐇); m-8 (the first printed line of p.269); m-9 ((B) uses the inclusion alone). **Repaired** (§9.3).
- (ii) Λ′₀'s width via CRE p.256. **Repaired.**
- m-10 (consumer list): unchanged, since O1 is re-derived, not dropped. **No edit.**

## Status after round 24

- **OPEN:** O6 (new), O2, O2′, O3, O4, and D2.7's items.
- **For re-review in round 25:** O1 (P(n) gluing), §2.2–2.3 (O6, R-𝐁, R-fr), §5 (s5 minors 2–4), §5.6, §6.1 (gauge step), §7.1–7.2 (per-X ledger, fourth retreat mass), §9.3.
