# D2.6 closure: triage of round 26 (it1-d26-s{2,4,5,6,7,9}-20261025-r7; all six reports read in full; repairs 05:4x–06:08, 25 Oct, date)

Round 26 reviewed the closure after the round-25 repairs (WILSON_IT1_D26_TRIAGE_R25_2026_10_25.md). No fatal item. Serious: s4 S-1 and s2 S-1, S-2. All repaired below.

## s4 (§4, kind (γ))

No fatal; serious S-1; minors m-1 to m-3.
- S-1 (2.2/2.3's O6 status not carried into §4: "Derived" labels in 4.2(iii), 4.3, 4.5 covered complex σ_k): relabelled; 4.2 input (iii), 4.3's note and label, and 4.5 now say that over the ω-polydiscs at complex σ_k the bounds rest on O6. **Repaired** (relabelling).
- m-1 (the comparison constant between VAR's norm and |·| does not go into the factor 2 in general): c_V with |V − 1|_{VAR} ≤ c_V|V − 1| made explicit; ε_H ≤ C₁^{VAR}ε̄₁/(2c_V), ε₁ := max(data, 2c_Vε_H/C₁^{VAR}), ε_H ≤ 1. **Repaired** (4.2, map D2.1(4) *Constants*).
- m-2 (4.5 called O1 "OPEN"): "derived given R-ζ(b) and R-h, for re-review". **Repaired.**
- m-3 (uniformity of ε̄₁ in R not printed on a supplied page): VAR pages read and cited: p.279 l.28 (a₀, a₁, B₃ depend on d and L only), p.304 l.53, p.280 (C₁ absolute), p.293 (C₄), p.303 l.41 (B₃), (173) B₅ = 6B₁B₃C₁. [3]'s B₀, B₁ not re-read. **Repaired** (4.2).
- Observation (2.1(e) attributes C_S″b_k only to wrap groups failing (i) or (iii)): 2.1(e) now gives kind-(γ) wrap groups amplitude C_S″b_k and §4.2's per-slot bounds whether or not they fail (i) or (iii), as 4.3 states. **Repaired.**

## s5 (§5, the carry)

No fatal, no serious; issues 1–5.
- 1 (e^{c_W} not propagated): 5.0 Step 1/Step 3, "M_n := Σe^{c_W}w", map l.302 (ii′-a) and the l.308 stability bullet; 7.1's paragraph lists every species the factor covers (att(j, Z), the marks B_j(Z), C_{B,1}, lw). **Repaired.**
- 2 ((T0)'s window-reach term): (163 + C_win)M(ε^{new}_{re-run} + ε^{old}_n + ε^{ref,n}) ≤ ν_r/8, with the q = p₀ condition min(C₀, C₁) ≥ 8(163 + C_win)MK′C_T…, C₀, C₁ chosen after M (5.2, §8). **Repaired.**
- 3 (5.5's crossing count): L(E′_𝒢 + 2Σσ(D″)/L + 1) ≥ P, paid at (5/4)ν_e/L, so 2ν_e/L ≤ ν_r/16 for L ≥ 16 with ν_e ≤ ν_r/2; root factor T(D′); L ≥ 11 → L ≥ 16 everywhere. **Repaired** (5.5, §8).
- 4 (5.6's mark extent): 2ext₁ + 1 + d/(LM). **Repaired.**
- 5 (cosmetic and records): (T3)'s j(D″); the fragment in (T0); the c_D symbol clash with map (11)(a)'s c_D ≤ 81, renamed c_D^{chg} (5.2, §8); the R25 triage's s5 m-8 line ("No action") was wrong, corrected there (m-8 was 5.6's ℓ = LM_VR₁, repaired in round 25). **Repaired.**

## s6 (§6, the leading word)

No fatal, no serious; m1–m6.
- m1 (R-st's real part rested on the unsupplied Lemma c4-10-5): real part via row-locality (V3 L464, the stencil frame on 𝓔_c ⊆ 𝔓_c) and V3 L3740's site gauge, h ≤ 3c_Gc_hs_𝔓ε₀, condition 3c_Gc_hs_𝔓ε₀ ≤ τ_b/2; ‖Z‖ the max h-norm (V3 L4880). **Repaired** (6.1, §8).
- m2 (R-st's label), m3 (§8's protected input, now C(1+r)+1), m4 (61/16 annotations: map l.318, LINE_DEFECT l.954, l.961, l.1135), m5 (class (III) "not small in g₀": sentence corrected with the polydisc term), m6 (a′ rename; 6.2's r_C citation to CRE p.245 via V3 L3968). **Repaired.**

## s7 (§7, the payment)

No fatal, no serious; m-a to m-g. Verdict: correct and sufficient once m-a, m-b are written in.
- m-a (host cutoff parts): V3 L2732 bounds the cutoff part through 1 − Θ⁰ ≤ Σ_b(1 − χ⁰_b), not a decomposition. Telescoped exactly, 1 − Π_kχ⁰_{b_k} = Σ_k(Π_{i<k}χ⁰_{b_i})(1 − χ⁰_{b_k}); each piece ≤ 𝟏_{S_{b_k}} on the support, anchored at e(b_k); N_host = 4⁴·20⁴ hosts per bond (V3 L2633). No constant changes. **Repaired** (7.1 *Host cutoff parts*).
- m-b (host-mark anchoring): host side ≤ 4M (V3 L2827 checked). Constant host marks: N_host per anchor, extent ≤ 3 π₁-sides, e^{3ν_e}. h-form and tilt marks: decay form of IT-1 §3j(5) (checked at LINE_DEFECT l.1736–1746), anchored at the nearest J₁(Λ) point (complex δℓ tilt: J_col(Λ), 6.3(d); J₁ ⊆ J_col ⊆ J(Λ)), μ_x/2 + μ_x/4 + μ_x/4 split, extent factor e^{3ν_e/(2L)}; C_h := (…)·max|E(Y)|·N_hostC_{μ/2}C_{μ/4}e^{ν_e}, g₀ × polylog; C_st (clash with 6.4) removed. **Repaired** (7.1 *Host marks*, per-Q display).
- m-c: ε_A(1) ≤ K₁/(8C_X) at j = 1. **Repaired** (7.2).
- m-d: C̄_A := e^{c_W}sup C_A(n). **Repaired** (7.1).
- m-e: 𝔅_Z defined explicitly. **Repaired** (7.1 inputs bullet).
- m-f: 7.1's heading and §8's §7.1–7.3 entry name O6 (j ≥ 2) and O4 (step-1 t > 0 species). **Repaired.**
- m-g: polylog wording (+ g₀ × polylog terms); N₁(Δ) ≤ c_CC_FLM as displayed (either constant suffices); C_{μ/4} defined; the j = 1 branch of (1.85) per Z, κ₁(Z) := (B₁ + ε_A(1) + K₁/(8C_X))(d₁′(Z)+1), Pol(Z) := 0, Pol(X) per X under O2; map (5)(f)'s 2C_lw g₀(r+1). §8's "L ≥ 4" and "round 25 … pending" were already gone. **Repaired.**

## s9 (§9, the carrier item and O1)

No fatal, no serious; m-1 to m-3 and nits. Verdict: correct and sufficient at the status of its Q3.
- m-1 (the exceptional bonds used V_i, which for i < k is integrated at step i+1): Û's data with Q^{s*}_iV_i^*; at the exceptional bonds V_i^* = V^{(i)}(V_{i+1}^*), so (A)'s argument is 0; in (B) X there is covered by the layer bound. **Repaired.**
- m-2 (unqualified "closed" in 9.3's header and closing and in 9.4): each now reads "derived given R-ζ(b), R-h and R-ζ(a) beyond Ω_{i+1}^∼, for re-review". **Repaired.**
- m-3 (the layer reasoning presupposes the axial gauge; R-ζ(a) beyond Ω_{i+1}^∼): V_i's regularity from p.256; χ_Ax on □′^{∼4}∖□′^{∼2} named as input (R-ζ(b) on the ring, R-ζ(a) beyond); the layer bound labelled as p.266's reasoning transferred (REG (1.65) p.87 under (1.33)–(1.35), p.82), not derived from REG; R-ζ(a) added to route (a)'s label. **Repaired.**
- Nits: "R-ζ" → "R-ζ(a)"; U_{i+1,□′} in the 𝔹_mix regular space; V^{(i)}_{□′} on □′^{∼4} means M^i(U_{i+1,□′}); p.269's printed "|_{Λ_k∩Ω_{k+1}}" read as Ω_{k+1}ᶜ against the determining set printed above it (CRE p.269 transcription l.28, l.32 checked; no note there); §8 lists O1 for tracking only. **Repaired.**

## s2 (§§0–3)

No fatal; serious S-1, S-2; m-1 to m-7.
- S-1 (the "derived" label on (1)'s potentials, and O6's scope): Bałaban's expansion uses localised terms, not raw functions (RG2 Lemma 2 p.11, 𝐏^{(k)} with the 𝐄_k-bracket; CRE p.276 l.36–49 for 𝐑_k and 𝐁_k, read; p.277 for A(·)), all bounded on (3.43) or (1.34). O6 widened to all localised terms with Y ⊄ Λ_{k+1}; "derived" kept for the raw sup bounds, the source term and A(·)'s analyticity; closure route widened (RG2 §1 Lemmas 1–2 and p.276's 𝐁_k-localisation with B = (A_k, A)). R2 now reads "at complex σ_k: NOT DERIVED (O6)". **Repaired** (relabelling; 2.2 (1), (1′), label; R2; §8's O6).
- S-2 (per-bond source factors e^{x_b} broke the species rule): the source term is localised through Bałaban's random-walk expansion of K = C*Δ_kC (RG2 p.13: "This construction was discussed in [13] for all operators determining Δ_k"; (1.6)–(1.7) p.3; p.5's δ₀d(ω) ≥ δ₁mM), x_X := ⟨A, K_Xζ⟩ with X meeting the σ_k-bonds; KP per cube Σ_{X∋Δ}2|x_X|e^{a·m(X)} ≤ 2dM^dB₀e^{32a}r_kr_{ω,k}, under δ₁M ≥ 2a (Bałaban's δ₁M ≥ κ₁ with 2a) and small g_k. 2.1's rule (i), 2.2's first paragraph and §2.4's support statement then hold at complex σ_k. **Repaired** (2.2 (2), 2.2 first paragraph, §2.4, §8 conditions).
- m-1 (O6 qualifiers on the rooted-sum heading, the (ii)-form label, §2.4's label, §2.5's reference clause, R2). **Repaired.**
- m-2 (A(·)'s size at complex σ_k): p.277's bound is a (3.43) bound, under O6; suppression by 𝐇_k's decay at complex B′ is R-dec; §2.3 *Complex σ_k* sentence replaced. **Repaired.**
- m-3 ((3.27)'s source term has no t). **Repaired.**
- m-4 (O1 status in R6, R14, §3's label): "derived given R-ζ(b) and R-h, for re-review". **Repaired.**
- m-5 (the gloss "A, the system of large-field fluctuation fields" is not printed on p.261): marked as part of R-src. **Repaired.**
- m-6 (R15 names R-fr and the widened O6). **Repaired.**
- m-7 (RG1's V(H₁B′) definition): quoted, "terms of at least third order in H₁B′" (RG1 p.266 l.39, checked). **Repaired.**

## Status after round 26

Open: O6 (widened: every localised term with Y ⊄ Λ_{k+1} at complex σ_k over the ω-polydiscs; consumers §2.2–2.5, §4.2(iii), §4.3, §4.5, §5.0, §7.1–7.3), O2, O2′, O3 (widened in round 25), O4, D2.7. O1 derived given R-ζ(b), R-h and R-ζ(a), for re-review. Round 27 needed: s2 (S-1, S-2 repaired, S-2 a new derivation) and s7 (m-a, m-b rewritten); s4, s5, s6, s9 repairs were relabellings or local and can be re-read in the same round.
