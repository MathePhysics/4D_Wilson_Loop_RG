# LF Packet 1, Review 3: Triage

Review: verification\isolated_reviewer\reviews\lf-p1-20261104-r3\review.md (LF bcd45850b90e). Verdict: ESTABLISHED EXCEPT ONE STEP; no fatal item. LF after the repairs: 2fa9f7052cd3, labels d448bd0024f9.

## Serious

1. **Decay of 1 − P_𝒮 (#0.1.17, last sentence).** Accepted. The sentence is replaced by the weighted test of #A.9:
   - ω := (P_NΔ↾N_b)^{−1}P_N∂₁*f satisfies ⟨∂ω, ∂ζ⟩ = ⟨f, ∂ζ⟩ on N_b;
   - the test field is ζ := w²ω − Σ_y mean_y(w²ω)b_y;
   - the per-block Poincaré bound then gives ‖e^{±δρ}∂ω‖ ≤ C(d)‖e^{±δρ}f‖ for δ ≤ c(d).

## Minor

2. **Q₁ and Δ_j under the conjugation.** Accepted. The text now uses the Hermitian part, K(cosh(δΔρ) − 1) = O(δ²)L^{−2}‖B‖², and cites PRT2 p.250 l.21 for the decay of Δ_j. The mass term commutes.
3. **Which form is F.** Accepted. F′ := (2.120) is the form that C̃ inverts (PRT2 p.248 l.42–43). F′ ≥ F by (2.118), with a = 1 (p.244 l.2), and F_g := F′ + ‖P_N∂₁*B‖².
4. **Coarse crossing bonds in Λ′.** Accepted: PRT2 p.224 l.17–19 is cited in #0.1.16.
5. **#A.9 (iii), the source E₁^Tf.** Accepted: G_B(E₁^Tf) ≤ C(d)αr sup abs(f).
6. **#A.9, the frame of the inputs.** Accepted. The inputs are conjugated by Ad(g_t^{−1}), as the data transform (REG p.78 l.15, checked).
7. **VAR (190) on the complex domain.** Accepted: VAR p.309 l.2–3 is cited, checked.

## Packet-2 rework, in the same LF revision

- The hole-filling runs below s₃ := min(L/8, t₃(x₀)/C(d)) (#0.1.20, #0.1.23, #A.7). Its Morrey bound is E(Q_r) ≤ C(d)(r/L)^α(L/t₃)^αĒ.
- In those cubes, #A.1 shows two things: the cells of Λ^c form one local component, and every contact of codimension ≥ 2 is locally joined.
- #A.2 introduces the feet. #A.3 starts the Dirichlet potential at the feet and runs it through the free crossing bonds.
- #A.4 uses closing paths through the diagonal cell, with arc fluxes. The false sentence "One box cannot touch two distinct components" is removed.
- #A.5 drops the H¹ jump sentence.
- The factor (L/t₃)^{α/2} is carried through:
  - #0.1.26;
  - (K2) and (K3), with the (1 + log L)^{p+1} bound at r ≤ L/16 for (K4);
  - (K5), as (r_m/t₃(z))^μ;
  - (K6), where W absorbs it because κ ≥ 1 − α/2 and t ≤ t₃.
- (K3)'s sentence on codimension-2 joins through the corner site is removed.

## Next

p1 r4, with prior = the r3 review. p2 r1 follows after two clean passes of p1.