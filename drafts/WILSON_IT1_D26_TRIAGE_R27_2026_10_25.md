# D2.6 closure: triage of round 27 (it1-d26-s{2,4,7}-20261025-r8; all three reports read in full; repairs 06:19–06:3x, 25 Oct, date)

Round 27 re-reviewed §§0–3 (s2), §4 (s4) and §7 (s7) after the round-26 repairs (WILSON_IT1_D26_TRIAGE_R26_2026_10_25.md). All three ran on claude-opus-5-5. No fatal item. Serious: s4 S-A (a labelling error). Repaired below.

## s2 (§§0–3)

No fatal or serious item; minors n-1 to n-9 and two observations. All repaired.
- n-1 (walk bound for Δ_k): the source-term localisation now cites the walk expansions Bałaban proves for the propagators that determine Δ_k: PBG p.416 (3.108), p.427 (walk expansions of G₁, H₁, Δ^{(2)}_π with the estimates of (3.108)) and p.428 (Δ_k = (3.156); C "almost local"; uniform exponential decay of C*Δ_kC), read in the transcription, together with RG2 p.13. They are Bałaban's proved results, used as such.
- n-2: X(ω) := ∪X̃_j^5 enlarged by C's range; B₀ → C_KB₀, with C_K = C_K(d, M, M₁, a) absorbing the rooting factor (M/M₁)^d and 1/(ea); condition C_KB₀e^{32a}r_kr_{ω,k} ≤ c_KP (§2.2(2), §8, map D2.2(6)(e)).
- n-3: e^{−x_X} − 1; "𝐔 on X".
- n-4: the normaliser expansion is "the shifted-potential expansion under O6".
- n-5: O6 qualifiers on §2.2's *Size* bullet and on 2.1(e)'s kind-(γ) amplitude C_S″b_k.
- n-6: R1, R5, R12 carry "at real σ_k; over the ω-polydiscs at complex σ_k: O6".
- n-7: O1 "derived given R-ζ(b), R-h and R-ζ(a)" in R6, R14 and §3.
- n-8: header and sources (RG2 pp.3–5, 9–13, 15; PBG pp.416, 427–428).
- n-9: R-fr added to R15 in both parts.
- Observations: map D2.2(6)(e) *The radii* rewritten per localisation domain with C_KB₀e^{32a}; §5.3's label names O6.

## s4 (§4, kind (γ))

No fatal; serious S-A; minors m-A to m-E; nits n-a to n-d; one observation.
- S-A (the "derived at real σ / O6 at complex σ" split does not separate a derived case): the ω-dependent att members are evaluated at R(w(s,t))ω, which is complex at every complex point of the (s, t_Y)-polydisc even at real outer σ (map D2.2(4)(f), (4)(g), (6)(e)). So these members rest on O6 with no derived case; 4.3, 4.5 and their labels are relabelled.
- m-A: 4.2's label adds "input (iii) for att members over the ω-polydiscs NOT DERIVED (O6)", and ε_H ≤ 1.
- m-B: 4.5's O1 status is "derived given R-ζ(b), R-h and R-ζ(a)"; the label names S-A's consequence and the ω-radius amendment.
- m-C (uniformity of ε̄₁ in VAR's R): now derived from printed dependences, each read: C₁ (VAR p.280), C₄ (p.293), B₃ (p.303), B₅ ((173), p.305); B₀ (PBG pp.423–424, "depend on d and L only"); B₁ (REG p.83, Theorem 2). VAR's M is the regularity-cube parameter, M ≤ M(ε₁) = R₁M₁(a₁/ε₁), and "M′ε₁ ≤ a₁" restricts M's range, not ε₁.
- m-D: the (ii)-only kind-(γ) groups also rest on O6 over the polydiscs, since the Kotecký–Preiss inputs of 2.2's re-run are stated for the whole gas.
- m-E: 4.2(iii) now says dev members take their bounds from (T-dev), not from O6.
- n-a: 4.1's label lists CRE (2.5) and (2.7).
- n-b: the comparison |V − 1|_{VAR} ≤ c_V|V − 1| is stated, and used, on {e^{iX} : |X| ≤ ε_H} only (4.2); globally it fails for a non-faithful π (V = −1 in SU(2)'s adjoint).
- n-c: 4.3 says 2.2's C covers the costs of (γ1), e^{(5/8)ν_e}, and of (γ2), e^{ν_e/2}.
- n-d (round-26 n-1, n-2 not recorded): round-26 s4 n-1 (layer width with R = R_k) was carried out in 4.1 from CRE (2.5) and (2.7): a layer-j width ≥ 6LMR_{j+1} > 6MR_k/(1+β₀) ≥ M₁R_k for β₀ ≤ 5. Round-26 s4 n-2 ("ε_H ≤ 1 since ε_H < ε₃^{RG2}" needs ε₃^{RG2} ≤ 1) was carried out by adding ε_H ≤ 1 to map D2.1(4) *Constants* and to 4.2.
- Observation (map superscripts): D2.1(4) now reads C₁^{RG2}ε₁^{RG2} ≤ ε₃^{RG2}, ε_H < ε₃^{RG2}, "C₁^{RG2} of RG2 (1.20)", and g_k|A_k| ≤ ε_H/C₁^{RG2} (map l.210, l.420, l.497, l.499, l.500, l.509, l.510, l.969).

## s7 (§7)

No fatal or serious item; minors M1 to M4; nits. All repaired. Verdict: correct and sufficient for its stated purpose, with O2, O2′, O3, O4 and O6 open.
- M1 (one host term with two anchors at complex data): a host's smooth part is one term, and its bound is the sum of the h-form, real-tilt and complex δℓ-tilt forms. All three are taken in the J_col(Λ) form (J₁(Λ) ⊆ J_col(Λ)), and the term is anchored at one nearest point of J_col(Λ). C_{μ/2} is a sum over all bonds, so it serves both sets. 5.6's anchor list adds J_col(Λ) points and the bonds b_W of M4.
- M2: the complex δℓ constant is named, C^δ_bdρ₁ϑr² (IT-1 l.1125, 𝔪^δ_Y ≤ C^δ_bdρ₁ϑr²Σ_{b:Y_b=Y}Σ_ee^{−μ_Hd(b,e)}), and it enters C_h. The support sentence "within R_N + ρ_L of J₁(Λ)" is restricted to the real tilt and marked unused.
- M3: C̄_A^{(j+1)} := e^{c_W}sup_{n≥j+1}C_A(n) (7.2, used in 7.3).
- M4 (one anchor per term for the inputs and att(1, ·) parts): 7.1 *One anchor per term*.
  - (a) The inputs term is split exactly into one piece per input b, by the chain rule along the shift. Each piece is bounded by V3 Lemma c5-5-7z(b)'s per-direction assertion (read, V3 L2737–2747, L2783). It is anchored at b → Z, or retreat-anchored.
  - (b) A group that is not good and whose Q_W lifts has a target bond with an endpoint in Q_W (IT-1 §3a(4)(i), §3d(4), read). Its background part is anchored at the first such bond b_W, and d(n, b_W) ≤ diam Q_W + 1 ≤ C_boxLM𝔰(W) + 1 gives §3d(4)'s per-traversal decay from b_W. Groups whose Q_W does not lift are wrap(1).
- Nits: C_sh′; m̄_h with ω̄̂ (IT-1 §3j(4)(c), l.1728); tie order for the nearest input of constant host marks; one booking rule (the nearest ℓ-cube of Ret(Λ)); #E(Q) ≤ 2dℓ^d.

## Status after round 27

Open: O6 (every localised term with Y ⊄ Λ_{k+1} at complex σ_k over the ω-polydiscs, including the ω-dependent att members at real outer σ, s4 S-A), O2, O2′, O3, O4, D2.7. O1 is derived given R-ζ(b), R-h and R-ζ(a), for re-review.

Round 28 covers s4 (S-A's relabelling) and s7 (M4's new derivation); s2 had no serious item.
