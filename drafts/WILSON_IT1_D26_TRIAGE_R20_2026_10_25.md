# Round-20 triage of the D2.6 closure (reports read 00:11–00:25, 25 Oct 2026, date)

Reports: verification/isolated_reviewer/reviews/it1-d26-s{2,4,5,6,7,9}-20261024-r1/review.txt (claude-opus-5-5, xhigh; returned 23:41–23:48, 24 Oct). No fatal finding in any report. Dispositions below; "applied" = repaired in WILSON_IT1_D26_CLOSURE_2026_10_24.md in this pass, "amended" = the closure now carries a changed statement for the user's review, "OPEN" = reverted to open with its location.

## Status line

OPEN after triage: (O1) R14's band cubes with □′^{∼4} ⊄ Ω_{i+1} (s9 S1: the localisation identity (3.17) needs the constraints on □′^{∼4} to be those of 𝔹_{i+1}(□′^{∼4}); on the Γ_i-part they are the scale-i constraints; the extended (3.19) would force |V_i(V^{(i)}_{□′})^{−1} − 1| ≪ δ_i on Γ_i-bonds, against (3.3)'s 2δ_i). (O2) the extra label of IT-1 §3c(4⁗)(d) (s6 S4: §6.5 reduces §3j(0) to it; the step map accepting the merged label activities is not derived; not D2.6's, D2.2(3)(b)'s). (O3) the k = 1 base point on Ω₁∖Ω₂ (s2 S2; D2.2(6)(e), already OPEN there; §3 and §5.1 use it at k = 1). (O4) s5 S1's per-position control: resolved by the lineage form of §5 (new argument, for review), not by a per-position bound.

## s2 (§0–§3)

| # | Finding | Disposition |
|---|---|---|
| S1 | collar rate κ_s/2 in 2.2/2.4 not available (κ_s spent by (14)(c)–(e)); 2.4's κ/(2L) never compared with η_V/C_F | applied: one mechanism everywhere, the extent weight: att(k+1, ·) groups carry e^{ν_e ext} inside (S-w); half of it ((ν_e/2)ext) pays the distance to the collar/component at rate c_* := ν_e/4 per π-side, the other half is carried (§5.0). D(k)(ii)'s collar rate lowered to c_*′ := min(η_V/C_F, ν_e/4, κ/(4L)) (amended; V3's step-1 bound implies the weaker rate) |
| S2 | §3's deviation bound on Ω_k∖Ω_{k+1} rests on R-m beyond p.277 and on the OPEN k = 1 base point | applied: labelled "given R-m (k ≥ 2) and the OPEN k = 1 base point of D2.2(6)(e)" (O3); q₀ > q₁ branch deleted |
| m1 | 2.1(a): per-t form not supplied; sup → sum | applied: paid by the extent weight alone, no w_t |
| m2 | b_k = C₁A₁g_k(log)^{p₀}; chain constant 1/(2C′_χ) | applied |
| m3 | traversal count c_C(M+2r); N ≤ 2c_CMC_N; C_B gains 2M | applied |
| m4 | σ_k support: the σ_k-bonds (Ω_{k+1}∩Λ_{k+1}ᶜ)^{(k)*} | applied |
| m5 | §1: components of Z_{k+1} = Λ_{k+1}ᶜ | applied |
| m6 | 2.2 radius sentence; D2.4(10) at ω′ ≠ 0 | applied: sentence removed; the measure's ω′-dependence (source term) is pointwise on the support, D2.4(10) runs at fixed ω′ (stated as the input) |
| m7 | R-B basis p.276 "remaining terms"; (2.47) j = n quote; slots → measure potentials; A(·) suppression sentence; (b3) | applied |
| m8 | 2.4: reading label; factor 2; flat factors not θ; one species test (Coll_{k+1}) | applied |
| m9 | 2.5: reference point by uniformity (D2.2(6)(c)); domain 𝒟^{sub} | applied |
| m10 | §3 arithmetic (factor L, rate < η_w/C_box, R_{t+1}, per-component via W → Z); complex-data bound | applied; complex data on 𝒟^{sub} by SW (b2)'s tail sum |
| m11 | wrap(k+1) not produced in §2 | applied: wrap(k+1) rule added to 2.1 (map l.278: Q_W does not lift) |
| m12 | undocumented rule changes (att(k+1, coll) for (i)/(iii) failures; override of "Q_W meets a component") | applied: logged in 2.1 for review |
| m13 | cosmetic (8 layers; units; (G2) clause; P_kp_k; "by summation"; 2^d) | applied |

## s4 (§4)

| # | Finding | Disposition |
|---|---|---|
| S1 | CRE p.276 l.2–16 sends older-scale terms to the boundary terms; potentials with Y ⊄ Λ_{k+1} are on (3.43) | applied: boundary-type potential := every 𝐃-potential with Y ⊄ Λ_{k+1}, plus 𝐁_k, A(·), V^{(k)}; kind (γ) with ω′ = 0 and no such potential has all potentials in Λ_{k+1}, (11)(f) verbatim; otherwise att(k+1, coll), O(b_k) |
| S2 | (11)(c)'s three further inputs | applied: (i) R-dec's O(1)(Lθ)^{k−m}h_k ≤ O(1)h_k per older-layer bond with c_πc_CM·O(1)h_k ≤ 1; (ii) a′ ∈ 𝒟^{sub}_{k+1} (the att clause is asserted on 𝒟^{sub}, for review); (iii) touched att/lw/wrap members bounded by their sup bounds (§5.1) |
| m1–m12 | wording, citations, partition, O(1) in ϑ, r′_k, gradient/curvature/𝐉 parts, parity wording, component rule, arc factor (now the extent mechanism), labels, 𝐇-part on crossing bonds | applied |

## s5 (§5)

| # | Finding | Disposition |
|---|---|---|
| S1 | rooted sums with carried att members as per-position W-vertices; only totals are controlled | applied: lineage form. The multilinear expansion fixes the set S of old att insertions on a term; the rooted sums of (14)(d)–(e) are run over the NEW constituents only, rooted at the fixed old vertex ((14)(e)'s F(v₀) ≤ λb(v₀)e^{b(v₀)/2}); the product Π_D(1 + m_D) over the lineages replaces the species sum (new argument, for review) |
| S2 | κ′ = κ_s/4 not available | applied: κ′ := ν_e, reserved per π_n-cube of the components in (14)(e)'s count (amendment of κ_s^{(14)} by an additive constant, for review) |
| S3 | E_𝒢 charged to θ | applied: paid from the shares sh(v) of (14)(c); carried att members carry the reserve weight e^{ν_rσ_j(W)} as well (amended (ii′)) |
| S4 | extent definitions differ; SW §0(a) misquoted; double use | applied: ext^{coll} defined; (ν_e/2)ext^{coll} carried, the other half spent; SW §0(a) cited as a scope statement with (14)'s count the actual source |
| S5 | domain inconsistent (full vs 𝒟^{sub}) | applied: att bounds on 𝒟^{sub} at production and in (ii′), as complex-data bounds; inclusion from SW (b3)–(b4) under O(1)Lθ ≤ (1−β)/min(β,1) |
| S6 | supp B′ ⊆ Ω_{n+1}, not Λ_{n+1} | applied throughout (T1), (T3), 5.3, 5.5 |
| S7 | R-run not printed; Cor. 8.2 is cumulative | applied: R-run deleted; S_R ≤ (2 + C/b)(f(X) + g_*²/b) from Cor. 8.2's form u_k ≥ u_K + b(K−k) − C (Bałaban project, simple G); the coupling upper bound is again a user (recorded) |
| S8 | rooting vs species | applied: root at the first-species member; the lineage form has no cross-feeding issue |
| m1–m13 | units (π_n-side M), citations (3.5)/(3.20), (1.84)–(1.88) not on p.385, Cauchy factor 2, ≤, e^{θ_{n+1}}, R-cpl₀, ε^{new} (3c_n), merging wording, no anchored Y₀, lw via §6, q − p₀, per-traversal normalisation | applied |

## s6 (§6)

| # | Finding | Disposition |
|---|---|---|
| S1 | f_ξ's i-th term is contour-wide | applied: subset expansion for f_ξ too; map l.279's one-insertion form amended (lw slots compatible, Q = 1) for review |
| S2 | Y_i depends on U₁ and ω | applied: Y_i is B-independent, U₁- and ω-dependent; sup bound on 𝒟^{sub}_1 with the complex-background factor (1 + (log g₀^{−2})^{(q₁−p₀)₊}) of §3j(6); carried by §5 |
| S3 | per-bond size circular; 𝓕_r-dependence; exposed links | applied: ‖Y_i‖ ≤ C_link g₀Σ_{b∈𝓕_{r_i}}h(m̂_b) (V3 Lemma c5-5-7z(a), L2737); exposed-link term ≤ C_link g₀ r|𝓕| for links with 𝓕_{r_i} ∩ J(Λ) ≠ ∅; R_lw gains 2R_c |
| S4 | §3g(2) factorises χ_Λ only; count check; extra label | applied: the operation stated (merge the label polymers meeting N_S into the S-term's activity; cost e^{a_lab|N_S|}); the acceptance of merged activities by the step map = the extra label, OPEN at D2.2(3)(b)/IT-1 §3c(4⁗)(d) (O2) |
| m1–m9 | Λ₁ᶜ ⊆ Z₁; c_J; C_μ with (2D+3)⁴; l.276 citation; R_lw ≤ MR₁; thresholds; round-8 status; budget; ordered products | applied |

## s7 (§7)

| # | Finding | Disposition |
|---|---|---|
| S1 | the enlarged induction is a re-run, not Bałaban's statement | applied: relabelled derived; the checks listed ((1.82) with 4(64)^d; (1.83) verbatim; (1.84)–(1.87) with (d′+1) subadditive up to 4dC_A; #cubes via S^m(Z) ⊆ S^m(X) ∪ S^m(Y); (1.88) with 6(100M)^d; p.387's sums; p.386 small domains; (1.89)) |
| S2 | κ₁ display drops −O(1)M^dR₁^{d+1}d₁′ and spends all of κ₁ | applied: j = 1 condition strengthened to 8(64)^d; c_LF from the reserved eighth |
| S3 | ρ̂ ≤ τ² needs q₁ < 3p₀ | applied: τ̂² := max(τ², Cρ̂) in 7.4(a) and 7.2 |
| S4 | inputs term of A_j(Z) missing | applied: j = 1 term 2C_lw′g₀ϑ_VrMR₁-type from §3j(5); j ≥ 2: absent by §2.2's construction (ω′-dependence bounded pointwise, no translation) |
| S5 | linking of e_X across components at general k | applied: 7.4(b)'s two comparisons stated at every step with the reserved eighth and τ̂² |
| m1–m14 | C̄_A; 1/32; p₀ large (not 2p₀ > r(d+2)); d′ specified; ε_A once; E_j vs D_j; (T) retired → (14)(d); §3i(0)'s form; count-check label; misattributed quote; wording; m12; m13 unverifiable; m14 | applied |

## s9 (§9)

| # | Finding | Disposition |
|---|---|---|
| S1 | (3.17) fails for □′ with □′^{∼4} ⊄ Ω_{i+1} | OPEN (O1). §9.3 kept for □′ with □′^{∼4} ⊂ Ω_{i+1} (no reading needed there). Readings R-avg, R-reg2 withdrawn from the derived part (R-avg kept as a reading of (3.10)/p.267 for 9.2). Route (a) recorded with what VAR Prop. 9/(190) gives (the global response to a ≤ 3δ_i change of the Γ_i-data is ≤ 3C′δ_i/L in scale-i averages) and what is missing (the localisation identity for the mixed set on □′^{∼4}: CMP98 (106)–(108), (159)–(163) for mixed sets, or Bałaban's p.269 usage); route (b) ((LPG′) on the multi-scale regularity class, 4t-r2) for the user |
| m1–m14 | pointer D2.4(5)(2); ε conversion (1+β₀)²; 44d² scaling; δ-function parenthetical; (2.9) citation; □^{∼4} extent; V_i^* near ∂Ω_i (R-avg, (1.3) locality); (3.15) quote; ζ dependency (R-h); units; §9.4; domain of (3.19); boundary-layer input; [16] | applied |
