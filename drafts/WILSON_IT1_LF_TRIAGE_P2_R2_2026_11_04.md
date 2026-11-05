# LF Packet 2, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p2-20261104-r2\review.md (LF 5a49532aab8f). Verdict: established as written for the N_b problem, d = 4, with no fatal or serious item. This is the first clean pass of packet 2. All minors are accepted and applied.

## Minor

1. **#0.1.21, the distance of R_η.** Accepted. It now reads "at distance ≥ 7s/64 from ∂Q_s and ∂Q_{s/2}".
2. **#0.1.24, the exponent ν.** Accepted. One sentence now turns the hitting probability into osc_{Q_r(x)}λ ≤ (1 − c(d))osc_{Q_{Kr}(x)}λ plus the cell and barrier terms, for the scalar problem Δλ = σ, by the barrier and optional stopping of (K5). So ν := log(1/(1 − c(d)))/log K.
3. **θ_B as a definition.** Accepted. #0.1.27 now defines {#D.θ_B} θ_B := L² sup abs(g′) in the N_b problem: the units of the field, in which C̃ = O((1 + log L)²L²). The table is not edited.
4. **#A.4 (iv), abs(m(x′) − m(x)) ≤ 1.** Accepted. The bound is now stated only where m(x) or m(x′) is < ρ₁/4 + 1, the only case needed, since otherwise ϑ = 0 at both ends.
5. **#0.1.23, the product-rule shift.** Accepted. The shift reads φ_A − φ_Q at the endpoint where χ ≠ 0, so only where φ_A is defined.
6. **#0.1.24, "≤ 2^d blocks".** Accepted. It now reads "≤ C(d) coarse bonds c whose two blocks meet Q_s".

## Found in the self-check of packets 3 and 4 during r2

- **Q₁ normalisation (#0.1.18, #0.1.24, #0.1.26).** The review read the LF's Q₁ profile L^{1−d} as given. PRT2 p.245 prints (Q₁B)(c) = Σ_{x∈B(c₋)}L^{−(d+1)}B([x, x + Le_μ]), a block average with profile ≤ L^{−d}, and p.243 writes the form as aL^{d−2}Σ_cabs(Q₁B(c))². The three places are corrected:
  - #0.1.18: the Q₁-terms are L^{d−2}Σ_c(Q₁u)(c)q_c, with profiles ≤ L^{−d} on two blocks and coefficients ≤ C(d)L^{d/2−2}‖u‖, so ≤ C(d)L^{−2−d/2}‖u‖ pointwise;
  - #0.1.24: the coarse terms are ≤ C(d)L^{d−2}Σ_c abs(Q₁u(c))abs(Q₁(η²w)(c)), with abs(Q₁u(c)) ≤ C(d)(1 + log L)^pθ and abs(Q₁(η²w)(c)) ≤ C(d)L^{−d}s^{d/2}‖w‖_{Q_s}. Young's inequality gives (s/L)^{d+2}Ē, the same exponent;
  - #0.1.26: the Q₁ part of R²sup abs(h₁) is ≤ C(d)L^{−d/2}‖u‖_{Q_{2L}} ≤ C(d)(1 + log L)^pθ (#A.10).

  The conclusions are unchanged.
- **#0.1.14, (2.146).** B₁ is Q″*B except on the bonds of ∪Ax(y), where it is 0 (p.248). The bound is now ≥ C(d)^{−1}‖B₁‖².
- **#0.1.14, the axial example.** The text now states the gauge function: λ = −1 beyond the first tree bond, plus the block constant making Q′λ = 0. So Q₁B = Q₁δ = O(L^{−d}), ‖B‖² ≥ L^{d−1}, and Σ abs(∂₁B)² = 2(d − 1). The paths Γ_{y,x} run along e_d first, by p.244. This is compared with the printed constant L^{−d−1}/(12d²) of (2.128).

## Next

The text of packet 2 changed in #0.1.23, #0.1.24, #0.1.26, and #A.4, so the second clean pass is p2 r3 on LF 12d07fa2eacc.
