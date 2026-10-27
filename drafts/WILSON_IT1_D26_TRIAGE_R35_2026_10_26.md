# D2 map: triage of round 35

Round 35 re-reviewed the round-34 repairs. The reviews ran headless in the CLI (`claude -p`, claude-opus-5-5, effort high, launcher `verification\isolated_reviewer\run_app_review_cli.ps1`), at the user's request ("Start them in the CLI"). Reports:
- `it1-rc-p6-20261026-r2\review.md`: R-c Pass 6, the collar step;
- `it1-hc-20261026-r2\review.md`: translation covariance (RTR_PROOF_PASS, map D2.3(5));
- `it1-rh-a-20261026-r2\review.md`: R-𝐇, the passage to 𝐇^{(j)} and analyticity (map l.970–973);
- `it1-rh-b-20261026-r2\review.md`: R-𝐇, the domain and the inclusion (map l.971, l.975–984).

Every report was read in full. Each serious finding was checked against the cited pages before repair.

## Open after this round

- **OPEN: the base points on Ω₁∖Ω₂.** Missing: the real part of (2.34) at n = 1 and (2.38) for U₂ on Ω₁∖Ω₂. The gap is rooted at k = 1 and reaches every k through (4)(f) (j = 0, 1). What closes it: map l.976 (a)–(b).
- **OPEN: the gauge frame of σ_j** (D2.2(4)(d)). Missing: how 𝐇^{(j)} transforms under the step's gauge transformation w. What closes it: the representative item D2.2(4)(d).
- **Not re-reviewed:** RC_PROOF_PASS Pass 6 (f); the new forms of R-𝐇 (map l.971–975), *What it closes* (l.984) and the summary at l.222.

## rc-p6 (R-c Pass 6)

- **S1 (serious): Pass 6 covered real backgrounds only.** Confirmed: D(1)(iii) needs the cutoffs on Ũ^c₁(X), and Pass 6 used V4's real mean shift. Repair: new Pass 6 (f), a real-base shift. At 𝐔 = U′U shift by m_t(U), so the cutoffs stay real. The remainder is (i) δH quadratic (RG2's R₁, R₂ of (2.16)), (ii) the linear term −t⟨A″, w⟩, w = δH_{DD}m(U) + δH_{DJ}A_e (RG2's −⟨B, R₃X⟩, p.16), and (iii) constants, which cancel. RG2 (2.21) bounds it by O(α_{0,1} + α_{1,1})r² = O(g₀ polylog) per collar bond. The pieces are integrals over real A′ against a Gaussian density centred at m_t, entire in the shift. V4 (I1)–(I3) at U: Lemma regular-bounds' proof needs only a local gauge with ‖A‖_∞ ≤ μ̂, which (2.38) supplies with μ̂ = O(BCMα_{0,1}).
- **S2: the rounds.** Confirmed: Lemma c5-3-1(b) holds for LINE_DEFECT's 𝒬⁺ (l.119), not for the rounds as written. Repair: Pass 6 (a) uses 𝒬⁺; the carrier is cited as V4 L2404, L2480.
- **Minors m-a to m-e.** ρ_L − 1 in place of ρ_L, via a free bond with an endpoint at y, with J₁(Λ) ⊂ J_col(Λ) by Lemma c5-1-2. The norm caveat |A″|_σ² ≤ N h(A″)², N = c_h², with Nγ₂ under (LM)⁴γ₂ ≤ 1. The bonds are b ∈ D(Λ). Repaired in Pass 6 (b)–(e) and map l.185, l.188.

## hc (translation covariance)

- No serious finding.
- Repaired: m1 (RTR l.113: the 𝐄-terms only; CRE (2.32), p.260, for the R-terms); m2 (map l.1010: δm^σ, and δm_1 = −(4L)^{−1}Σκ_v); m3 (V4 line numbers +80, checked against the TeX: L1574, L1595, L1612, L1649, L1702, L1710, L1720, L1763, L1772, L1130, L1362, L1097, L1101–L1108); m4 (RTR l.44: CMP98 (64)–(72), (77), RG1 p.252); m5 (RTR l.115: a translation-covariant local selection rule; on flat data the representative is unique); m7 (map l.353: Π_{k+1}-periodic); m8 (map l.1020: the localised 𝐄-activities).
- m6 (fix C in the (e₁, e₂) plane, as V4 L1519): not applied. It is an optional simplification, and D2 already works per plane with the averages.

## rh-a (passage to 𝐇^{(j)}, analyticity)

- **S1 (serious): the Schwarz bound lost a factor L^{n_b} and treated u as fixed.** Confirmed. CMP98 (128)–(129) give the averaged phase after n levels < 2α₁L^nη for an input field bound α₁, so the polydisc radius is ρ_b = (c₃/4)L^{−n_b}. u = u(h) depends on the argument: VAR p.307 ("This transformation is an analytic function of 𝓗"), CMP98 (106). Repair (map l.972): B_b is enlarged to the top-level blocks of b's endpoints, u's phases are added to the modulus, and |𝐇^{(j)}(b)| ≤ C_{d,L}L^{n_b}sup_{B_b}|h|. The factor L^{n_b} cancels against (190)'s (L^{j_x}η)^{−1}, since n_b ≤ j ≤ j_x, so S_H stands. This matches p.268/(3.19), which is O(1) times the bound on 𝐇.
- **m2: the frame links.** (i) By the identity theorem, U_k(XV″V₀′)U₀^{−1} = e^{iη𝓗(X;U₀)} at complex V″ (p.307; p.309/Prop. 9). (ii) p.309 covers the G^c transformation. Repaired in l.972.
- **m3:** VAR §F → Sect. G throughout the map.
- **m6:** the choice of ε₁ is the larger of V₀'s curvature bound in (7) and 2α_{1,n}/C₁^{VAR}, ≤ a₁.
- **m7:** Prop. 3 is applied in the Landau frame (field-small by VAR (19); in the axial frame only phase-small, REG p.80) and carried to the axial frame by u.
- **m8:** CRE (1.3) multiplicativity for the reference data.
- **m9:** "Its inputs at 𝐔 ∈ Ũ^c_{j+1}" → 𝒰_j.
- **Decay (l.973).** The separation is ≥ LMR_{j+1} − 2LM₁ ≥ ½LMR_{j+1}. The condition is (δ₀/32)LM ≥ L+1, a condition on M, which CRE p.245 chooses last ("M will be chosen much larger than M₂"). The units of d are those of [3], used by p.268; [3] is not in the local set. Updated at l.222, 973, 981, 984.
- **C_H list.** C₁^{CRE} and C₁^{CMP} are distinguished, B₅ is added, L also enters through L^{n_b}, and C is dropped.

## rh-b (domain, inclusion)

- **S-A (serious): the (2.35) derivation on Y_j does not hold.** Confirmed: VAR's level-indexed weights do not match CRE's layer weights in the collars of 𝔅_p(Y_j). Repair: (2.35) and (2.37) are dropped from 𝒰_j. REG (1.65) (p.87, l.36–40) uses only CMP98 Prop. 2's averages Ū^m of the configurations compared (|∂Ū^m − 1| < 2α₀L^{2m}η²). REG Lemma 1 (pp.79–80) is local (p.80), and p.268's input is U_{k+1}'s regularity alone. So (2.34) suffices, and the constant C is gone. Map l.971 (R-𝐇 statement), l.972 (argument-bound inputs), l.975 (the (2.35) derivation deleted; the claim reads 𝐔|_{Y_j} ∈ 𝒰_j), l.222, l.984.
- **m6:** D(k)(iii)'s k ≥ 2 amendment now says which conditions are global ((2.34), (2.36), (2.38), (2.39)) and that (2.35), (2.37) are posed on the domains X of the terms that use them (l.984).
- **m7:** R-𝐇₀ at complex external U is Bałaban's, through p.251 and p.309's extension ("All the above considerations and properties are valid for this function also"). Map l.980.
- **√d:** the cube-family match needs √d·CM < RM₁L (l.975).

## Files

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: 19fb341f1695 → 386b1426e7d7.
- RC_PROOF_PASS_2026_10_23.md: b6b95501d310 → 1e07c4713a81.
- READINGS_RECHECK_2026_10_23.md: d860cd54acb4 → b63d9833db14 (rows 2, 28, 35 and the summary).
- RTR_PROOF_PASS_2026_10_23.md: 53536791b1a2 → 2d7c298f53eb.
